
#include "cx/fileb.h"
#include "cx/sys-cx.h"

#include <assert.h>
#include <ctype.h>

typedef struct Pair Pair;
typedef struct Function Function;
typedef struct NamedFunction NamedFunction;
typedef struct Runtime Runtime;
typedef struct TypeInfo TypeInfo;
typedef struct InternalTypeInfo InternalTypeInfo;

typedef size_t pkey_t;


DeclTableT( Pair, Pair );
DeclTableT( Function, Function );
typedef TableT(Function) FunctionSet;
DeclTableT( NamedFunction, NamedFunction );
DeclTableT( TypeInfo, TypeInfo );
DeclTableT( InternalTypeInfo, InternalTypeInfo );

DeclTableT( pkey_t, pkey_t );
#ifndef DeclTableT_uint
#define DeclTableT_uint
DeclTableT( uint, uint );
#endif
#ifndef DeclTableT_cstr
#define DeclTableT_cstr
DeclTableT( cstr, char* );
#endif
#ifndef DeclTableT_ccstr
#define DeclTableT_ccstr
DeclTableT( ccstr, const char* );
#endif


enum known_types_enum
{
    AnyType,
    FunctionInternalType,
    VarArgInternalType,
    CStringInternalType,
    YesType,
    NilType,
    ConsType,
    ListType,
    NKnownTypes
};


enum FunctionType
{
    StandardFunc, InternalFunc,
    ConstructFunc, AccessFunc,
    SetOfFunc,
    PendingDefFunc, NFuncTypes
};
typedef enum FunctionType FunctionType;



struct Pair
{
    pkey_t key;
    void*  val;
};

struct Function
{
    unsigned nargs;
    pkey_t*  types;
    FunctionType type;
    union function_struct_union
    {
        struct function_struct_regular_case
        {
            unsigned nexprs;
            unsigned nsubst;
            Pair* exprs;
            unsigned* argmap;
        } std;
        struct function_struct_internal_case
        {
            void (* f) (Pair*, void*);
            void* extra;
        } internal;
        struct function_struct_type_case
        {
            pkey_t type;
        } construct;
        struct function_struct_access_case
        {
            unsigned idx;
        } access;
            /* TODO: Unused.*/
        struct function_struct_pending_case
        {
            TableT(Pair) parsed;
        } pending;
        struct function_struct_multi_case
        {
            FunctionSet funcs;
        } set;
    } info;
};

struct NamedFunction
{
    char* name;
    Function* f;
};

struct Runtime
{
    TableT(Pair) d; /* Data stack.*/
    TableT(Pair) e; /* Expression stack.*/
};

struct TypeInfo
{
    char* name;
    unsigned nmembs;
    pkey_t* types;
};

struct InternalTypeInfo
{
    void* (* copy_fn) (const void*);
    void  (* free_fn) (void*);
    void (* write_fn) (FileB*, const void*);
};


static pkey_t ScratchPKey;
static TableT(InternalTypeInfo) Internal_Types;
static TableT(TypeInfo) Named_Types;
static TableT(NamedFunction) Named_Functions;

#define HIGHBIT ((pkey_t)1 << (NBits_byte * sizeof (pkey_t) -1))
static const pkey_t MUTABIT = HIGHBIT >> 1;
static const pkey_t CALLBIT = HIGHBIT;
#undef HIGHBIT
#define StripPKey(k)  (k & ~(MUTABIT | CALLBIT))

#define HIGHBIT ((pkey_t)1 << (NBits_byte * sizeof (uint) -1))
static const uint WILDBIT = HIGHBIT;
#undef HIGHBIT
#define StripWildBit(k)  (k & ~WILDBIT)

#define PtrTo(Type, p)  ((Type) (size_t) (p))
#define ToPtr(i)  ((void*) (size_t) (i))


static int streqlP (const char* a, const char* b)
{
    return 0 == strcmp (a, b);
}

static int mutableP (const Pair* pair)
{
    return !!(MUTABIT & pair->key);
}

static void set_mutable_P (Pair* pair, int b)
{
    if (b)  pair->key |=  MUTABIT;
    else    pair->key &= ~MUTABIT;
}

static int funcallP (const Pair* pair)
{
    return !!(CALLBIT & pair->key);
}

static void set_funcall_P (Pair* pair, int b)
{
    if (b)  pair->key |=  CALLBIT;
    else    pair->key &= ~CALLBIT;
}

static int fixarg_func_P (const Function* f)
{
    return !(WILDBIT & f->nargs);
}

static void set_fixarg_func_P (Function* f, int b)
{
    if (b)  f->nargs &= ~WILDBIT;
    else    f->nargs |=  WILDBIT;
}

static int vararg_func_P (const Function* f)
{
    return WILDBIT == f->nargs;
}

static void set_vararg_func_P (Function* f, int b)
{
    if (b)  f->nargs = 0;
    set_fixarg_func_P (f, !b);
}

static int macro_func_P (const Function* f)
{
    return !fixarg_func_P (f) && f->types;
}

static void set_macro_func_P (Function* f, int b)
{
    if (b)  f->types = &ScratchPKey;
    set_fixarg_func_P (f, !b);
}

static int simple_type_P (const TypeInfo* info)
{
    return !(WILDBIT & info->nmembs);
}

static void set_simple_type_P (TypeInfo* info, int b)
{
    if (b)  info->nmembs &= ~WILDBIT;
    else    info->nmembs |=  WILDBIT;
}

static int compound_type_P (const TypeInfo* info)
{
    return !simple_type_P (info) && info->types;
}

static int internal_type_P (const TypeInfo* info)
{
    return !simple_type_P (info) && !info->types;
}

static const TypeInfo* type_info (pkey_t type)
{
    assert (type < Named_Types.sz);
    return &Named_Types.s[type];
}

static const InternalTypeInfo* internal_type_info (const TypeInfo* info)
{
    unsigned i;
    assert (internal_type_P (info));
    i = (unsigned) StripWildBit(info->nmembs);
    return &Internal_Types.s[i];
}

static
    unsigned
num_type_members (pkey_t type)
{
    return StripWildBit(type_info (type) -> nmembs);
}

static
    void
write_CString (FileB* out, const char* str)
{
    dump_cstr_FileB (out, str);
}

static
    void
write_Pair (FileB* out, const Pair* pair)
{
    pkey_t type;
    const TypeInfo* info;
    if (funcallP (pair))
        type = FunctionInternalType;
    else
        type = StripPKey(pair->key);
    assert (type < Named_Types.sz);
    info = type_info (type);
    if (internal_type_P (info))
    {
        const InternalTypeInfo* internal;
        internal = internal_type_info (info);
        assert (internal->write_fn);
        (*internal->write_fn) (out, pair->val);
    }
    else
    {
        unsigned i;
        dump_char_FileB (out, '(');
        dump_cstr_FileB (out, info->name);
        pair = (Pair*) pair->val;

        for (i = 0; i < info->nmembs; ++i)
        {
            dump_char_FileB (out, ' ');
            write_Pair (out, &pair[info->nmembs - i - 1]);
        }
        dump_char_FileB (out, ')');
    }
}

static
    void
write_Function (FileB* out, const Function* f)
{
    unsigned i, nargs;
    if (SetOfFunc == f->type)
    {
        const FunctionSet* fs;
        const char* name;
        name = "funcs";
        printf_FileB (out, "(%s", name);
        fs = &f->info.set.funcs;
        for (i = 0; i < fs->sz; ++i)
        {
            dump_char_FileB (out, ' ');
            write_Function (out, &fs->s[i]);
        }
        dump_char_FileB (out, ')');
        return;
    }

    if (macro_func_P (f))  dump_cstr_FileB (out, "(macro");
    else                   dump_cstr_FileB (out, "(func)");

    nargs = StripWildBit(f->nargs);
    for (i = 0; i < nargs; ++i)
    {
        const TypeInfo* info;
        pkey_t t;
        dump_char_FileB (out, ' ');
        if (macro_func_P (f))  t = AnyType;
        else                   t = f->types[f->nargs -i -1];
        info = type_info (t);
        dump_cstr_FileB (out, info->name);
    }
    dump_char_FileB (out, ')');
}

static
    void
write_Runtime (FileB* out, const Runtime* run)
{
    unsigned i;
    dump_cstr_FileB (out, "Expression stack:\n");
    for (i = 0; i < run->e.sz; ++i)
    {
        write_Pair (out, &run->e.s[i]);
        dump_char_FileB (out, '\n');
    }
    dump_cstr_FileB (out, "Data stack:\n");
    for (i = 0; i < run->d.sz; ++i)
    {
        write_Pair (out, &run->d.s[i]);
        dump_char_FileB (out, '\n');
    }

    if (0 != run->e.sz)
    {
        const Pair* const expr = TopTable( run->e );
        if (funcallP (expr))
        {
            dump_cstr_FileB (out, "Current function:\n");
            write_Pair (out, expr);
            printf_FileB (out, "\nnargs: %u\n", (uint) StripPKey(expr->key));
        }
    }
}

static
    void
cleanup_Pair (Pair* pair)
{
    const TypeInfo* info;
    pkey_t typei;
    typei = StripPKey(pair->key);
    assert (typei < Named_Types.sz);
    info = type_info (typei);
    if (internal_type_P (info))
    {
        const InternalTypeInfo* internal;
        internal = internal_type_info (info);
        if (internal->free_fn)
            (*internal->free_fn) (pair->val);
        else
            assert (!internal->copy_fn);
    }
    else
    {
        assert (info->nmembs == StripWildBit(info->nmembs));
        if (info->nmembs)
        {
            unsigned i;
            pair = (Pair*) pair->val;
            for (i = 0; i < info->nmembs; ++i)
                cleanup_Pair (&pair[i]);
            free (pair);
        }
    }
}

static
    void
clear_TableT_Pair (TableT(Pair)* t)
{
    uint i;
    UFor( i, t->sz )  cleanup_Pair (&t->s[i]);
    t->sz = 0;
}

static
    void
set_pair (Pair* dst, const Pair* src)
{
    dst->key = src->key;
    dst->val = src->val;
}

static
    void
copy_Pair (Pair* dst, const Pair* src)
{
    pkey_t typei;
    const TypeInfo* info;
    typei = StripPKey(src->key);
    assert (typei < Named_Types.sz);
    info = type_info (typei);
    if (internal_type_P (info))
    {
        const InternalTypeInfo* internal;

        internal = internal_type_info (info);
        if (internal->copy_fn)
        {
            dst->key = mutableP (src);
            dst->val = (*internal->copy_fn) (src->val);
        }
        else
        {
            assert (!mutableP (src));
            assert (!internal->free_fn);
            set_pair (dst, src);
        }
    }
    else
    {
        if (!info->nmembs)
        {
            assert (!mutableP (src));
            set_pair (dst, src);
        }
        else
        {
            unsigned i;
            dst->key = MUTABIT | typei;
            dst->val = AllocT( Pair, info->nmembs );

            src = (Pair*) src->val;
            dst = (Pair*) dst->val;
            for (i = 0; i < info->nmembs; ++i)
                copy_Pair (&dst[i], &src[i]);
        }
    }
}

static
    int
typeofP (pkey_t a, pkey_t t)
{
    const TypeInfo* info;
    if (AnyType == t)  return 1;

    info = type_info (a);
    assert (!compound_type_P (info)
            && "Why check for compound type 'is a' compound type?");

    info = type_info (t);
    if (compound_type_P (info))
    {
        unsigned i, ntypes;
        ntypes = StripWildBit(info->nmembs);
        for (i = 0; i < ntypes; ++i)
            if (a == info->types[i])
                return 1;
    }
    return a == t;
}

static
    int
funcall_fit_P (unsigned nargs, const Pair* args, const Function* f)
{
    unsigned i;
    if (vararg_func_P (f))  return 1;
    if (macro_func_P (f))   return nargs == StripWildBit(f->nargs);
    if (nargs != f->nargs)  return 0;

    for (i = 0; i < nargs; ++i)
        if (!typeofP (StripPKey(args[i].key), f->types[i]))
            return 0;
    return 1;
}

static
    const Function*
find_function (unsigned nargs, const Pair* args, const Function* f)
{
    unsigned i;
    if (SetOfFunc == f->type)
    {
        const FunctionSet* fset;
        fset = &f->info.set.funcs;
        for (i = 0; i < fset->sz; ++i)
        {
            f = &fset->s[i];
            if (funcall_fit_P (nargs, args, f))  return f;
        }
        return 0;
    }

    if (funcall_fit_P (nargs, args, f))  return f;

    return 0;
}

static
    void
eval1 (Runtime* run)
{
    DecloStack( Pair, expr );
    *expr = *TopTable( run->e );
    MPopTable( run->e, 1 );

    if (funcallP (expr))
    {
        unsigned i;
        unsigned nargs;
        const Function* f;
        Pair* dsk;
        
        nargs = (unsigned) StripPKey( expr->key );

            /* How many args do you have, really? */
        assert (nargs == StripPKey( expr->key ));

        assert (run->d.sz >= nargs && "Not enough arguments.");

        run->d.sz -= nargs;
        dsk = Elt( run->d.s, run->d.sz );

        f = find_function (nargs, dsk, (Function*) expr->val);
        if (!f)
        {
            GrowTable( run->d, nargs );
            GrowTable( run->e, 1 );
            write_Runtime (stderr_FileB (), run);
            assert (f && "Bad function call - check types and nargs.");
        }
        dsk = 0;

        if (StandardFunc == f->type)
        {
            Pair* esk;
            unsigned nexprs;
            unsigned nsubst;
            unsigned* argmap;
            nexprs = f->info.std.nexprs;
            nsubst = f->info.std.nsubst;
            argmap = f->info.std.argmap;

            i = run->e.sz;
            GrowTable( run->e, nexprs ); 
            dsk = &run->d.s[run->d.sz];
            esk = &run->e.s[i];

                /* Build up the expression stack. */
            memcpy (esk, f->info.std.exprs, nexprs * sizeof (Pair));

                /* Substitute the arguments for formal parameters. */
            for (i = 0; i < nsubst; ++i)
            {
                unsigned dst_idx, src_idx;
                dst_idx = argmap[2*i];
                src_idx = argmap[2*i+1];
                assert (dst_idx < nexprs);
                assert (src_idx < nargs);
                if (!funcallP (&esk[dst_idx]))
                    esk[dst_idx].key = dsk[src_idx].key;
                esk[dst_idx].val = dsk[src_idx].val;
            }
                /* Handle mutable arguments. */
            for (i = 0; i < f->nargs; ++i)
            {
                unsigned j, min_dst;
                if (!mutableP (&dsk[i]))  continue;
                min_dst = nexprs;
                for (j = 0; j < nsubst; ++j)
                {
                    unsigned dst_idx;
                    if (i != argmap[2*j+1])  continue;
                    dst_idx = argmap[2*j];
                    if (dst_idx < min_dst)  min_dst = dst_idx;
                    set_mutable_P (&esk[dst_idx], 0);
                }
                if (min_dst == nexprs)
                    cleanup_Pair (&dsk[i]);
                else
                    set_mutable_P (&esk[min_dst], 1);
            }
        }
        else if (InternalFunc == f->type)
        {
            dsk = Grow1Table( run->d );
                /* This is a built-in function. */
            (f->info.internal.f) (dsk, f->info.internal.extra);
        }
        else if (ConstructFunc == f->type)
        {
            Pair* val = 0;
            dsk = Grow1Table( run->d );

            if (f->nargs)
            {
                val = AllocT( Pair, f->nargs );
                    /* This is a function to construct a type. */
                for (i = 0; i < f->nargs; ++i)
                {
                    if (mutableP (&dsk[i]))
                        set_pair (&val[i], &dsk[i]);
                    else
                        copy_Pair (&val[i], &dsk[i]);
                }
                dsk[0].key = f->info.construct.type;
                set_mutable_P (&dsk[0], 1);
            }
            else
            {
                dsk[0].key = f->info.construct.type;
            }
            dsk[0].val = val;

        }
        else if (AccessFunc == f->type)
        {
                /* This is a getter function. */
            unsigned i, get_idx, nmembs;
            Pair* membs;
            Pair tmp;
            assert (1 == f->nargs);
            dsk = Grow1Table( run->d );
            set_pair (&tmp, dsk);

            nmembs = num_type_members (StripPKey(tmp.key));
            get_idx = f->info.access.idx;
            assert (get_idx < nmembs);
            membs = (Pair*) dsk->val;

            if (mutableP (&tmp))
            {
                set_pair (dsk, &membs[get_idx]);
                for (i = 0; i < nmembs; ++i)
                    if (i != get_idx)
                        cleanup_Pair (&membs[i]);
                free (membs);
            }
            else
            {
                copy_Pair (dsk, &membs[get_idx]);
            }
        }
        else
        {
            assert(0 && "Unknown function type.");
        }
    }
    else
    {
        PushTable( run->d, *expr);
    }
}

static void eval1func (Runtime* run)
{
    int loopP = 1;
    while (loopP)
    {
        Pair* expr = TopTable( run->e );
        if (funcallP (expr))
            loopP = 0;
        eval1 (run);
    }
}

static void eval (Runtime* run)
{
    while (run->e.sz > 0)  eval1 (run);
    assert (1 == run->d.sz);
}

static Function* find_named_function (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Functions.sz; ++i)
    {
        NamedFunction* f = &Named_Functions.s[i];
        if (streqlP (f->name, name))
        {
            return f->f;
        }
    }
    return 0;
}

static void copy_Function (Function* dst, const Function* src)
{
    memcpy (dst, src, sizeof (Function));
    if (fixarg_func_P (src))
        dst->types = DupliT( pkey_t, src->types, src->nargs );
    if (StandardFunc == src->type)
    {
        dst->info.std.exprs = DupliT(Pair,
                                     src->info.std.exprs,
                                     src->info.std.nexprs);
        dst->info.std.argmap = DupliT(unsigned,
                                      src->info.std.argmap,
                                      2*src->info.std.nsubst);
    }
}

#if 0
static void copy_TypeInfo (TypeInfo* dst, const TypeInfo* src)
{
    dst->name   = DupliT( char, src->name, 1+strlen(src->name) );
    dst->nmembs = src->nmembs;
    dst->types  = DupliT( pkey_t, src->types, StripWildBit(src->nmembs) );
}
#endif

static void cleanup_Function (Function* f)
{
    switch (f->type)
    {
        case StandardFunc:
            free (f->info.std.exprs);
            free (f->info.std.argmap);
        case InternalFunc:
        case ConstructFunc:
        case AccessFunc:
            if (fixarg_func_P (f))
                free (f->types);
            break;
        case SetOfFunc:
            { BLoop( i, f->info.set.funcs.sz )
                cleanup_Function (&f->info.set.funcs.s[i]);
            } BLose()
            LoseTable( f->info.set.funcs );
            break;
        default:
            break;
    }
}

static void cleanup_NamedFunction (NamedFunction* namedfn)
{
    free (namedfn->name);
    cleanup_Function (namedfn->f);
    free (namedfn->f);
}

static void cleanup_TypeInfo (TypeInfo* info)
{
    if (info->name)
        free (info->name);
    if (StripWildBit(info->nmembs))
        free (info->types);
}

static void reverse_types (unsigned ntypes, pkey_t* types)
{
    unsigned i;
    for (i = 0; i < ntypes/2; ++i)
    {
        pkey_t tmp;
        tmp = types[i];
        types[i] = types[ntypes-i-1];
        types[ntypes-i-1] = tmp;
    }
}

static Function* force_init_named_function (const char* name)
{
    Function* f;
    DeclGrow1Table( NamedFunction, namedfn, Named_Functions );

    namedfn->name = dup_cstr (name);
    namedfn->f = AllocT( Function, 1 );
    f = namedfn->f;
    f->type = PendingDefFunc;
    f->nargs = 0;
    f->types = 0;
    return f;
}

static Function* ensure_named_function (const char* name)
{
    Function* f;
    f = find_named_function (name);
    if (!f)  f = force_init_named_function (name);
    return f;
}

static Function* add_named_function (const char* name, const Function* f)
{
    Function* f_new;
    f_new = ensure_named_function (name);
    assert (NFuncTypes > f_new->type);
    assert (!vararg_func_P (f_new) && "Cannot def over a vararg function.");
    assert (!vararg_func_P (f) && "Existing vararg function def.");
    if (PendingDefFunc != f_new->type
        &&   SetOfFunc != f_new->type)
    {
        Function tmp = *f_new;
        InitTable( f_new->info.set.funcs );
        PushTable( f_new->info.set.funcs, tmp );
        f_new->type = SetOfFunc;
    }

    if (SetOfFunc == f_new->type)
    {
        FunctionSet* fset = &f_new->info.set.funcs;
        f_new = Grow1Table( *fset );
    }
    copy_Function (f_new, f);
    if (fixarg_func_P (f_new))
        reverse_types (f_new->nargs, f_new->types);
    if (StandardFunc == f->type)
    {
        unsigned i;
        unsigned* argmap;
        argmap = f_new->info.std.argmap;
        for (i = 0; i < f_new->info.std.nsubst; ++i)
            argmap[2*i+1] = f_new->nargs - argmap[2*i+1] - 1;
    }
    return f_new;
}

static pkey_t force_init_type (const char* name)
{
    DeclGrow1Table( TypeInfo, info, Named_Types );
    pkey_t typei = Named_Types.sz - 1;

    if (name)  info->name = dup_cstr (name);
    else       info->name = 0;
    info->nmembs = 0;
    set_simple_type_P (info, 0);
    info->types = &ScratchPKey;
    return typei;
}

static pkey_t ensure_named_type (const char* name)
{
    unsigned i;
    assert (name);
    for (i = 0; i < Named_Types.sz; ++i)
    {
        const char* str;
        str = Named_Types.s[i].name;
        if (str && streqlP (str, name))
            return i;
    }
    return force_init_type (name);
}

static pkey_t add_simple_type (const TypeInfo* src, const char* const* membs)
{
    unsigned i;
    Function f;
    pkey_t type;
    TypeInfo* dst;

    type = ensure_named_type (src->name);
    dst = &Named_Types.s[type];

    f.nargs = src->nmembs;
    f.types = src->types;
    f.type = ConstructFunc;
    f.info.construct.type = type;
    add_named_function (src->name, &f);

    dst->nmembs = src->nmembs;
    dst->types  = DupliT(pkey_t, src->types, src->nmembs);
    reverse_types (dst->nmembs, dst->types);

    f.nargs = 1;
    f.type = AccessFunc;
    for (i = 0; i < src->nmembs; ++i)
    {
        f.types = &type;
        f.info.access.idx = src->nmembs - i - 1;
        add_named_function (membs[i], &f);
    }

    assert (!compound_type_P (dst) && !internal_type_P (dst));
    return type;
}

static pkey_t add_compound_type (const TypeInfo* src)
{
    pkey_t type;
    TypeInfo* dst;

    type = ensure_named_type (src->name);
    dst = &Named_Types.s[type];

    dst->nmembs = src->nmembs;
    set_simple_type_P (dst, 0);
    dst->types  = DupliT(pkey_t, src->types, src->nmembs);
    
    assert (compound_type_P (dst));
    return type;
}

static
    pkey_t
add_internal_type (const char* name, const InternalTypeInfo* iinfo)
{
    pkey_t typei;
    TypeInfo* info;
    if (name)  typei = ensure_named_type (name);
    else       typei = force_init_type (0);
    info = &Named_Types.s[typei];
    info->nmembs = Internal_Types.sz;
    set_simple_type_P (info, 0);
    info->types = 0;
    PushTable( Internal_Types, *iinfo );
    assert (internal_type_P (info));
    return typei;
}

static pkey_t find_named_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Types.sz; ++i)
    {
        const char* str;
        str = Named_Types.s[i].name;
        if (str && streqlP (str, name))
            return i;
    }
    assert (0 && "Unknown type.");
    return AnyType;
}

static void push_function (Runtime* run, const char* name, pkey_t nargs)
{
    Pair expr;
    expr.key = nargs;
    set_funcall_P (&expr, 1);
    expr.val = find_named_function (name);
    assert (expr.val && "Function not found.");
    PushTable( run->e, expr );
}

static
    uint
parse_list (TableT(Pair)* t, char* str)
{
    unsigned i = 1;
    unsigned nmemb = 0;  /* #args + 1 */
    unsigned diff = 1; /* Re-used state. */
    unsigned toki; /* Current token index. */

    if (str[0] != '(')  return 0;
    str[0] = 0;

    toki = t->sz;
    GrowTable( *t, 1 );

    while (1)
    {
        if (!str[i])
        {
            diff = 0;
            break;
        }
        else if (!isgraph (str[i]))
        {
            diff = 1;
            str[i++] = 0;
        }
        else if (str[i] == ')')
        {
            diff = i+1;
            str[i] = 0;
            break;
        }
        else if (str[i] == '(')
        {
            ++ nmemb;
            diff = parse_list (t, &str[i]);
            if (!diff)  break;
            i += diff;
        }
        else
        {
            if (diff)
            {
                DeclGrow1Table( Pair, tok, *t );
                ++ nmemb;
                diff = 0;
                tok->key = CStringInternalType;
                tok->val = &str[i];
            }
            ++ i;
        }
    }

    if (diff)
    {
        Pair* fntok = &t->s[toki];
        fntok->key = nmemb;
        set_funcall_P (fntok, 1);
        fntok->val = (void*) (t->sz - (size_t) fntok->val);
    }
    else
    {
            /* If there was a failure, revert parse tree. */
        t->sz = toki;
    }
    return diff;
}


static pkey_t interp_deftype (const char* str)
{
    unsigned i;
    pkey_t typei;
    TypeInfo info;
    DeclTable( pkey_t, types );
    Pair* node;
    DeclTable( Pair, parsed );
    char* buf = dup_cstr (str);

    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");
    assert (!str[i]);

    assert (parsed.sz > 1);

    node = &parsed.s[0];
    assert (funcallP (node) && "Plain value at toplevel?!");

    node = &parsed.s[1];
    assert (streqlP ("deftype", (char*)node->val));

    node = &parsed.s[2];
    if (funcallP (node))
    {
        DeclTable( ccstr, membs );

        node = &parsed.s[0];
        assert (2 == StripPKey(node->key));

        node = &parsed.s[3];

        info.name = (char*) node->val;

        for (i = 4; i < parsed.sz; ++i)
        {
            const char* membstr;
            const char* typestr;
            node = &parsed.s[i];
            if (funcallP (node))
            {
                unsigned nelems;
                nelems = StripPKey(node->key);
                assert (2 == nelems && "Missing type for type param!");

                node = &parsed.s[++i];
                assert (!funcallP (node));
                membstr = (char*) node->val;

                node = &parsed.s[++i];
                typestr = (char*) node->val;
            }
            else
            {
                membstr = (char*) node->val;
                typestr = "any";
            }

            PushTable( membs, membstr );
            PushTable( types, ensure_named_type (typestr) );
        }

        assert (membs.sz == types.sz);
        info.nmembs = types.sz;
        info.types = types.s;

        typei = add_simple_type (&info, membs.s);

        LoseTable( membs );
    }
    else
    {
        info.name = (char*) node->val;

        for (i = 3; i < parsed.sz; ++i)
        {
            const char* typestr;
            node = &parsed.s[i];
            assert (!funcallP (node));
            typestr = (char*) node->val;
            PushTable( types, ensure_named_type (typestr) );
        }

        if (3 == parsed.sz)
        {
            const TypeInfo* chkinfo;
            typei = find_named_type (info.name);
            chkinfo = type_info (typei);
            assert (internal_type_P (chkinfo));
        }
        else
        {
            info.nmembs = types.sz;
            info.types = types.s;
            typei = add_compound_type (&info);
        }
    }

    LoseTable( parsed );
    LoseTable( types );
    free (buf);
    return typei;
}

static void interp_def (const char* str)
{
    const unsigned formals_offset = 4;
    char* funcname;
    unsigned i;
    Function func;
    DeclTable( Pair, parsed );
    DeclTable( pkey_t, types );
    DeclTable( cstr, formals );
    DeclTable( Pair, exprs );
    DeclTable( uint, argmap );
    Pair* node;
    char* buf = dup_cstr (str);

    
    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");

    assert (parsed.sz > 1);

    node = &parsed.s[0];
    assert (funcallP (node));
    assert (2 == StripPKey(node->key) || 3 == StripPKey(node->key));

    node = &parsed.s[1];
    assert (streqlP ("def", (char*) node->val));

    node = &parsed.s[2];
    assert (funcallP (node) && "Non-functions not supported yet in def's.");
    func.nargs = StripPKey(node->key);
    assert (func.nargs > 0);
    -- func.nargs;

    node = &parsed.s[3];
    assert (!funcallP (node));
    funcname = (char*) node->val;

    func.type = StandardFunc;
        /* TODO: macros */
        /* func.type = ('\'' == funcname[0]) ? MacroFunc : StandardFunc; */

        /* TODO: macros */
    if (macro_func_P (&func))
        assert (1 == func.nargs && "Macros only take one list argument.");

    for (i = formals_offset; types.sz < func.nargs; ++i)
    {
        const char* typestr;
        char* formalstr;
        node = &parsed.s[i];
        
            /* TODO: macros */
        if (macro_func_P (&func))
            assert (!funcallP (node) && "Use implied macro param type.");

        if (funcallP (node))
        {
            unsigned nelems;
            nelems = StripPKey(node->key);
            assert (2 == nelems && "Missing type for func param!");

            node = &parsed.s[++i];
            assert (!funcallP (node) && "(def ((name) arg1 arg2)) ?!");
            formalstr = (char*) node->val;

            node = &parsed.s[++i];
            typestr = (char*) node->val;
        }
        else
        {
            typestr = "any";
            formalstr = (char*) node->val;
        }

        PushTable( types, find_named_type (typestr) );
        PushTable( formals, formalstr );
    }

    for (; i < parsed.sz; ++i)
    {
        unsigned argi;
        const char* symname;
        Pair expr;

        node = &parsed.s[i];
        if (funcallP (node))
        {
            expr.key = StripPKey(node->key);
            assert (expr.key > 0);
            expr.key = (expr.key - 1);
            set_funcall_P (&expr, 1);

            node = &parsed.s[++i];
        }
        else
        {
            expr.key = 0;
        }

        assert (!funcallP (node));
        symname = (char*) node->val;

        for (argi = 0; argi < formals.sz; ++argi)
            if (streqlP (symname, formals.s[argi]))
                break;

        if (argi < formals.sz)
        {
            PushTable( argmap, exprs.sz );
            PushTable( argmap, argi );
        }
        else
        {
            expr.val = ensure_named_function ((char*) node->val);
            assert (expr.val && "Function not found.");
        }

        PushTable( exprs, expr );
    }

    if (0 == exprs.sz)
    {
        Pair expr;
        DBog0( "No return value, assuming (nil)." );
        expr.key = 0;
        set_funcall_P (&expr, 1);
        expr.val = find_named_function ("nil");
        assert (expr.val && "Function not found.");
        PushTable( exprs, expr );
    }

    if (StandardFunc == func.type)
    {
        func.types = types.s;
        func.info.std.nexprs = exprs.sz;
        func.info.std.nsubst = argmap.sz / 2;
        func.info.std.exprs = exprs.s;
        func.info.std.argmap = argmap.s;
    }
    add_named_function (funcname, &func);

    LoseTable( parsed );
    if (func.nargs > 0)
    {
            /* Don't: */
            /* LoseTable(types); */
        LoseTable( formals );
    }
    cleanup_Function (&func);

        /* Don't: */
        /* LoseTable( exprs ); */
        /* LoseTable( argmap ); */

    free (buf);
}

static
    uint
parsed_to_sexpr (Pair* expr, const TableT(Pair)* parsed, unsigned i)
{
    Pair* node;
    unsigned elemi, nelems;
    assert (i < parsed->sz && "ProgErr, overrunning sexpr parse.");
    node = &parsed->s[i++];
    if (!funcallP (node))
    {
        expr->key = node->key;
        expr->val = node->val;
        return i;
    }

    nelems = StripPKey(node->key);

    for (elemi = 0; elemi < nelems; ++elemi)
    {
        expr->key = ConsType;
        expr->val = AllocT( Pair, 2 );
        expr = (Pair*) expr->val;

        i = parsed_to_sexpr (&expr[0], parsed, i);
        expr = &expr[1];
    }

    expr->key = NilType;
    expr->val = 0;
    return i;
}

static
    uint
eval_macro (Runtime* run, const TableT(Pair)* parsed, unsigned i)
{
    Pair* expr;
    unsigned nargs;
    assert (run->e.sz && "Nothing in expression stack.");
    expr = TopTable( run->e );
    assert (funcallP (expr) && "No function call atop expression stack.");
    nargs = StripPKey(expr->key);
    while (nargs)
    {
        DeclGrow1Table( Pair, expr, run->e );
        i = parsed_to_sexpr (expr, parsed, i);
        -- nargs;
    }
    eval1func (run);
    PushTable( run->e, *TopTable( run->d ) );
    MPopTable( run->d, 1 );
    return i;
}

static void parse_to_runtime (Runtime* run, const char* str)
{
    unsigned i;
    DeclTable( Pair, parsed );
    char* buf = dup_cstr (str);

    InitTable( run->d );
    InitTable( run->e );

    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");

    for (i = 0; i < parsed.sz; ++i)
    {
        Pair* node;
        node = &parsed.s[i];
        if (funcallP (node))
        {
            unsigned nargs;
            ++i;
            nargs = StripPKey(node->key);
            assert (nargs);
            -- nargs;

            node = &parsed.s[i];
            push_function (run, (char*) node->val, nargs);
            if ('\'' == ((char*) node->val)[0])
            {
                i = eval_macro (run, &parsed, i+1);
                -- i;
            }
        }
        else
        {
            Pair pair;
                /* Assume it's a function for now. */
            pair.key = FunctionInternalType;
            pair.val = find_named_function ((char*) node->val);
            assert (pair.val && "Function not found.");
            PushTable( run->e, pair );
        }
    }
    LoseTable( parsed );
    free (buf);
}

static void cleanup_runtime (Runtime* run)
{
    clear_TableT_Pair (&run->d);
    clear_TableT_Pair (&run->e);
    LoseTable( run->d );
    LoseTable( run->e );
    InitTable( run->d );
    InitTable( run->e );
}

static void
interp_eval (FileB* out, const char* str)
{
    DecloStack( Runtime, run );

    parse_to_runtime (run, str);

    eval (run);
    write_Pair (out, &run->d.s[0]);
    dump_cstr_FileB (out, "\n");

    cleanup_runtime (run);
}

static void assert_eql (const char* lhs, const char* rhs)
{
    Pair expr;
    DecloStack( Runtime, lhsrun );
    DecloStack( Runtime, rhsrun );

    parse_to_runtime (lhsrun, lhs);
    parse_to_runtime (rhsrun, rhs);

    eval (lhsrun);
    eval (rhsrun);

    if (lhsrun->e.sz < 3)
        GrowTable( lhsrun->e, 3 - lhsrun->e.sz);

    expr.key = 2;
    set_funcall_P (&expr, 1);
    expr.val = find_named_function ("eql");
    assert (expr.val && "Function not found.");
    copy_Pair (&lhsrun->e.s[0], &expr);
    copy_Pair (&lhsrun->e.s[1], &rhsrun->d.s[0]);
    copy_Pair (&lhsrun->e.s[2], &lhsrun->d.s[0]);
    clear_TableT_Pair (&rhsrun->d);
    clear_TableT_Pair (&lhsrun->d);
    eval (lhsrun);

    copy_Pair (&expr, &lhsrun->d.s[0]);
    assert (StripPKey(expr.key) == find_named_type ("yes")
            && "Evaluated expressions are not equal! lhs != rhs.");

    cleanup_runtime (lhsrun);
    cleanup_runtime (rhsrun);
}


static void
test_cases (FileB* out)
{
    (void) out;
    assert_eql ("(yes)",
                "(or (nil) (yes))");

    assert_eql ("(cons (yes) (nil))",
                "(list (yes))");

    assert_eql ("(nil)",
                "(map list (nil))");

    assert_eql ("(cons (nil) (cons (yes) (list (nil))))",
                "(map not (cons (yes) (cons (nil) (cons (yes) (nil)))))");

    assert_eql ("(list (yes))",
                "(car (list (list (yes))))");

    assert_eql ("(cons (nil) (list (yes)))",
                "(rev (cons (yes) (cons (nil) (nil))))");

    assert_eql ("(yes)",
                "(in (nil) (set (cons (yes) (cons (nil) (list (yes))))))");

    assert_eql ("('int -5)",
                "(- (+ ('int 1) ('int 1)) (+ ('int 2) ('int 5)))");
}

static void func_eql_fn (Pair* data, void* extra)
{
    (void) extra;
    data[0].key = (data[1].val == data[0].val) ? YesType : NilType;
}

static void int_macro_fn (Pair* data, void* int_types)
{
    int res;
    res = atoi ((char*) data->val);
    data->key = ((pkey_t*) int_types)[(0 == res) ? 0 : 1];
    data->val = ToPtr(res);
}

static void write_int_fn (FileB* out, const void* val)
{
    int i;
    i = PtrTo(int, val);
    printf_FileB (out, "('int %d)", i);
}

static void int_add_fn (Pair* data, void* zero_typei)
{
    data[0].val = ToPtr( PtrTo(int, data[1].val) + PtrTo(int, data[0].val) );
    if (!data[0].val)
        data[0].key = PtrTo(pkey_t, zero_typei);
}

static void int_negate_fn (Pair* data, void* extra)
{
    (void) extra;
    data[0].val = ToPtr( - PtrTo(int, data[0].val) );
}

static void init_lisp ()
{
    pkey_t typei;
    InitTable( Named_Types );
    InitTable( Internal_Types );
    InitTable( Named_Functions );

    {
            /* Add the /any/ type, it's hardcoded. */
        TypeInfo* info;
        typei = ensure_named_type ("any");
        info = &Named_Types.s[typei];
        info->nmembs = 0;
        set_simple_type_P (info, 0);
        assert (AnyType == typei);
    }

    {   /* Add internal types. */
        InternalTypeInfo internal;

        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn =
            (void (*) (FileB*, const void*)) &write_Function;
        typei = add_internal_type ("func", &internal);
        assert (FunctionInternalType == typei);

        internal.write_fn = 0;
        typei = add_internal_type ("'", &internal);
        assert (VarArgInternalType == typei);

        internal.write_fn =
            (void (*) (FileB*, const void*)) &write_CString;
        typei = add_internal_type (0, &internal);
        assert (CStringInternalType == typei);
    }

    {
        Function f;
        pkey_t types[2];
        f.nargs = 2;
        types[0] = FunctionInternalType;
        types[1] = FunctionInternalType;
        f.types = types;
        f.type = InternalFunc;
        f.info.internal.f = &func_eql_fn;
        add_named_function ("eql", &f);
    }

    typei = interp_deftype ("(deftype (yes))");
    assert (YesType == typei);
    typei = interp_deftype ("(deftype (nil))");
    assert (NilType == typei);
    typei = interp_deftype ("(deftype list cons nil)");
    assert (ListType == typei);
    typei = interp_deftype ("(deftype (cons car (cdr list)))");
    assert (ConsType == typei);
}

static void cleanup_lisp ()
{
    uint i;
    UFor( i, Named_Functions.sz )
        cleanup_NamedFunction (&Named_Functions.s[i]);
    LoseTable( Named_Functions );

    UFor( i, Named_Types.sz )
        cleanup_TypeInfo (&Named_Types.s[i]);
    LoseTable( Named_Types );

    LoseTable (Internal_Types);
}

int main ()
{
    FileB* out;
    init_sys_cx ();
    out = stdout_FileB ();
    init_lisp ();
    push_losefn_sys_cx (cleanup_lisp);

    interp_deftype ("(deftype bool yes nil)");

    interp_def ("(def (or (a yes) (b yes)) (yes))");
    interp_def ("(def (or (a yes) (b nil)) (yes))");
    interp_def ("(def (or (a nil) (b yes)) (yes))");
    interp_def ("(def (or (a nil) (b nil)) (nil))");

    interp_def ("(def (and (a yes) (b yes)) (yes))");
    interp_def ("(def (and (a yes) (b nil)) (nil))");
    interp_def ("(def (and (a nil) (b yes)) (nil))");
    interp_def ("(def (and (a nil) (b nil)) (nil))");

    interp_def ("(def (impl (a yes) (b yes)) (yes))");
    interp_def ("(def (impl (a yes) (b nil)) (nil))");
    interp_def ("(def (impl (a nil) (b yes)) (yes))");
    interp_def ("(def (impl (a nil) (b nil)) (yes))");

    interp_def ("(def (eql (a yes) (b yes)) (yes))");
    interp_def ("(def (eql (a yes) (b nil)) (nil))");
    interp_def ("(def (eql (a nil) (b yes)) (nil))");
    interp_def ("(def (eql (a nil) (b nil)) (yes))");

    interp_def ("(def (not (a nil)) (yes))");
    interp_def ("(def (not (a yes)) (nil))");

    interp_def ("(def (if (a nil) b c) c)");
    interp_def ("(def (if (a yes) b c) b)");

    interp_def ("(def (eql (a cons) (b nil )) (nil))");
    interp_def ("(def (eql (a nil ) (b cons)) (nil))");
    interp_def ("(def (eql (a cons) (b cons))"
                "  (and (eql (car a) (car b))"
                "       (eql (cdr a) (cdr b))))");

    interp_def ("(def (cat (a nil ) (b list)) b)");
    interp_def ("(def (cat (a cons) (b list))"
                "  (cons (car a)"
                "        (cat (cdr a) b)))");

    interp_def ("(def (list a) (cons a (nil)))");

    interp_def ("(def (rev (L nil)) (nil))");
    interp_def ("(def (rev (L cons))"
                "  (cat (rev (cdr L))"
                "       (list (car L))))");

    interp_def ("(def (map (f func) (L nil)) (nil))");
    interp_def ("(def (map (f func) (L cons))"
                "  (cons (f (car L))"
                "         (map f (cdr L))))");

    interp_def ("(def (consif (pred func) e L)"
                "  (if (pred e) (cons e L) L))");

    interp_def ("(def (filter (f func) (L nil)) (nil))");
    interp_def ("(def (filter (f func) (L cons))"
                "  (consif f (car L) (filter f (cdr L))))");

    interp_deftype ("(deftype (set (elements list)))");

    interp_def ("(def (in e (L nil)) (nil))");
    interp_def ("(def (in e (L cons))"
                "  (or (eql e (car L))"
                "      (in e (cdr L))))");
    interp_def ("(def (in e (S set))"
                "  (in e (elements S)))");

    {
        static pkey_t int_types[2];
            /* Add some internal integer stuff. */
        InternalTypeInfo internal;
        pkey_t int_typei;
        Function f;
        pkey_t types[2];

        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn = &write_int_fn;
        int_types[0] = add_internal_type ("zero", &internal);
        int_types[1] = add_internal_type ("nonzero-int", &internal);
        int_typei    = interp_deftype ("(deftype int zero nonzero-int)");

        f.nargs = 1;
        f.type = InternalFunc;
        set_macro_func_P (&f, 1);
        f.info.internal.f = &int_macro_fn;
        f.info.internal.extra = int_types;
        add_named_function ("'int", &f);

        f.nargs = 2;
        types[0] = int_types[1];
        types[1] = int_types[1];
        f.types = types;
        f.info.internal.f = &int_add_fn;
        f.info.internal.extra = ToPtr(int_types[0]);
        add_named_function ("+", &f);

        f.nargs = 1;
        types[0] = int_types[1];
        f.info.internal.f = &int_negate_fn;
        add_named_function ("-", &f);
    }

    interp_def ("(def (+ (a zero) (b zero)) a)");
    interp_def ("(def (+ (a zero) (b nonzero-int)) b)");
    interp_def ("(def (+ (a nonzero-int) (b zero)) a)");

    interp_def ("(def (- (a zero)) a)");

    interp_def ("(def (zero (a zero)) (yes))");
    interp_def ("(def (zero (a nonzero-int)) (nil))");

    interp_def ("(def (- (a int) (b int))"
                "  (+ a (- b)))");
    interp_def ("(def (eql (a int) (b int))"
                "  (zero (- a b)))");

    test_cases (out);

#if 0
#elif 0
    {
        const char* str =
            "(cat (cons (yes) (nil))"
            "     (cat (cons (nil) (cons (nil) (nil)))"
            "          (cons (yes) (cons (yes) (cons (yes) (nil))))))";
        interp_eval (out, str);
    }

#elif 0
    {
        const char* str =
            "(cons (cons (yes) (nil))"
            "      (cons (yes) (cons (yes)"
            "                        (and (nil) " /*...*/
            "(or (nil) (or (nil) (or (nil) (or (nil) (or (nil)" /*...*/
                /* yes */
            "(car (cons (yes) (cdr (cons (yes) (cons (yes) (nil))))))"
            ")))))"
            "))))";

        interp_eval (out, str);
    }
#endif

    interp_eval (out, "(list (yes))");

    lose_sys_cx ();

    (void) set_vararg_func_P;
    return 0;
}

