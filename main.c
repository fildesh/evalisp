
#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "array.c"
static Array Internal_Types;
static Array Named_Types;
static Array Named_Functions;

typedef size_t pkey_t;

#define NBitsInByte 8
#define HIGHBIT ((pkey_t)1 << (NBitsInByte * sizeof (pkey_t) -1))
static const pkey_t MUTABIT = HIGHBIT >> 1;
static const pkey_t CALLBIT = HIGHBIT;
#undef HIGHBIT
#define HIGHBIT ((pkey_t)1 << (NBitsInByte * sizeof (unsigned) -1))
static const unsigned WILDBIT = HIGHBIT;
#undef HIGHBIT

static pkey_t ScratchPKey;

#define PtrTo(Type, p)  ((Type) (size_t) (p))
#define ToPtr(i)  ((void*) (size_t) (i))

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

#define StripPKey(k)  (k & ~(MUTABIT | CALLBIT))
#define StripWildBit(k)  (k & ~WILDBIT)

struct pair_struct
{
    pkey_t key;
    void*  val;
};
typedef struct pair_struct Pair;

enum function_type_enum
{
    StandardFunc, InternalFunc,
    ConstructFunc, AccessFunc,
    SetOfFunc,
    PendingDefFunc, NFuncTypes
};
typedef enum function_type_enum FunctionType;

typedef Array FunctionSet;

struct function_struct
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
        struct function_struct_pending_case
        {
            Array parsed;
        } pending;
        struct function_struct_multi_case
        {
            FunctionSet funcs;
        } set;
    } info;
};
typedef struct function_struct Function;

struct named_function_struct
{
    char* name;
    Function* f;
};
typedef struct named_function_struct NamedFunction;

struct runtime_struct
{
    Array d; /* Data stack. */
    Array e; /* Expression stack. */
};
typedef struct runtime_struct Runtime;

struct type_info_struct
{
    char* name;
    unsigned nmembs;
    pkey_t* types;
};
typedef struct type_info_struct TypeInfo;

struct internal_type_info_struct
{
    void* (* copy_fn) (const void*);
    void  (* free_fn) (void*);
    void (* write_fn) (FILE*, const void*);
};
typedef struct internal_type_info_struct InternalTypeInfo;

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
    assert (type < Named_Types.n);
    return ARef( TypeInfo, Named_Types, type );
}

static const InternalTypeInfo* internal_type_info (const TypeInfo* info)
{
    unsigned i;
    assert (internal_type_P (info));
    i = (unsigned) StripWildBit(info->nmembs);
    return ARef( InternalTypeInfo, Internal_Types, i );
}

static
    unsigned
num_type_members (pkey_t type)
{
    return StripWildBit(type_info (type) -> nmembs);
}

static
    void
write_CString (FILE* out, const char* str)
{
    fputs (str, out);
}

static
    void
write_Pair (FILE* out, const Pair* pair)
{
    pkey_t type;
    const TypeInfo* info;
    if (funcallP (pair))
        type = FunctionInternalType;
    else
        type = StripPKey(pair->key);
    assert (type < Named_Types.n);
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
        fputc ('(', out);
        fputs (info->name, out);
        pair = (Pair*) pair->val;

        for (i = 0; i < info->nmembs; ++i)
        {
            fputc (' ', out);
            write_Pair (out, &pair[info->nmembs - i - 1]);
        }
        fputc (')', out);
    }
}

static
    void
write_Function (FILE* out, const Function* f)
{
    unsigned i, nargs;
    if (SetOfFunc == f->type)
    {
        const FunctionSet* fs;
        const char* name;
        name = "funcs";
        fprintf (out, "(%s", name);
        fs = &f->info.set.funcs;
        for (i = 0; i < fs->n; ++i)
        {
            fputc (' ', out);
            write_Function (out, ARef( Function, *fs, i ));
        }
        fputc (')', out);
        return;
    }

    if (macro_func_P (f))  fputs ("(macro", out);
    else                   fputs ("(func", out);

    nargs = StripWildBit(f->nargs);
    for (i = 0; i < nargs; ++i)
    {
        pkey_t t;
        fputc (' ', out);
        if (macro_func_P (f))  t = AnyType;
        else                   t = f->types[f->nargs -i -1];
        fputs (type_info (t) -> name, out);
    }
    fputc (')', out);
}

static
    void
write_Runtime (FILE* out, const Runtime* run)
{
    unsigned i;
    fputs ("Expression stack:\n", out);
    for (i = 0; i < run->e.n; ++i)
    {
        write_Pair (out, ARef(Pair, run->e, i));
        fputc ('\n', out);
    }
    fputs ("Data stack:\n", out);
    for (i = 0; i < run->d.n; ++i)
    {
        write_Pair (out, ARef(Pair, run->d, i));
        fputc ('\n', out);
    }

    if (0 != run->e.n)
    {
        const Pair* expr;
        expr = ARefLast( Pair, run->e );
        if (funcallP (expr))
        {
            fputs ("Current function:\n", out);
            write_Pair (out, expr);
            fprintf (out, "\nnargs: %u\n", (unsigned) StripPKey(expr->key));
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
    assert (typei < Named_Types.n);
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
    assert (typei < Named_Types.n);
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
        for (i = 0; i < fset->n; ++i)
        {
            f = ARef(Function, *fset, i);
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
    Pair* expr;

    expr = PopStack( Pair, run->e );

    if (funcallP (expr))
    {
        unsigned i;
        unsigned nargs;
        const Function* f;
        Pair* dsk;
        
        nargs = (unsigned) StripPKey( expr->key );

            /* How many args do you have, really? */
        assert (nargs == StripPKey( expr->key ));

        assert (run->d.n >= nargs && "Not enough arguments.");

        run->d.n -= nargs;
        dsk = ARef( Pair, run->d, run->d.n );

        f = find_function (nargs, dsk, (Function*) expr->val);
        if (!f)
        {
            GrowArray( Pair, run->d, nargs );
            GrowArray( Pair, run->e, 1 );
            write_Runtime (stderr, run);
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

            i = run->e.n;
            GrowArray( Pair, run->e, nexprs ); 
            dsk = ARef( Pair, run->d, run->d.n );
            esk = ARef( Pair, run->e, i );

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
            GrowArray( Pair, run->d, 1 );
            dsk = ARefLast( Pair, run->d );
                /* This is a built-in function. */
            (f->info.internal.f) (dsk, f->info.internal.extra);
        }
        else if (ConstructFunc == f->type)
        {
            Pair* val = 0;
            GrowArray( Pair, run->d, 1 );
            dsk = ARefLast( Pair, run->d );

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
            GrowArray( Pair, run->d, 1 );
            dsk = ARefLast( Pair, run->d );
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
        PushStack (Pair, run->d, expr);
    }
}

static void eval1func (Runtime* run)
{
    int loopP = 1;
    while (loopP)
    {
        Pair* expr;
        expr = ARefLast( Pair, run->e );
        if (funcallP (expr))
            loopP = 0;
        eval1 (run);
    }
}

static void eval (Runtime* run)
{
    while (run->e.n)  eval1 (run);
    assert (1 == run->d.n);
}

static Function* find_named_function (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Functions.n; ++i)
    {
        NamedFunction* f;
        f = ARef(NamedFunction, Named_Functions, i);
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
        dst->types = MemDup( pkey_t, src->types, src->nargs );
    if (StandardFunc == src->type)
    {
        dst->info.std.exprs = MemDup(Pair,
                                     src->info.std.exprs,
                                     src->info.std.nexprs);
        dst->info.std.argmap = MemDup(unsigned,
                                      src->info.std.argmap,
                                      2*src->info.std.nsubst);
    }
}

#if 0
static void copy_TypeInfo (TypeInfo* dst, const TypeInfo* src)
{
    dst->name   = MemDup( char, src->name, 1+strlen(src->name) );
    dst->nmembs = src->nmembs;
    dst->types  = MemDup( pkey_t, src->types, StripWildBit(src->nmembs) );
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
            CleanupArray( Function, f->info.set.funcs );
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
    NamedFunction* namedfn;
    Function* f;
    GrowArray( NamedFunction, Named_Functions, 1 );
    namedfn = ARefLast( NamedFunction, Named_Functions );
    namedfn->name = MemDup(char, name, 1+strlen(name));
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
        Function tmp;
        memcpy (&tmp, f_new, sizeof (Function));
        InitArray( Function, f_new->info.set.funcs, 2 );
        PushStack( Function, f_new->info.set.funcs, &tmp );
        f_new->type = SetOfFunc;
    }

    if (SetOfFunc == f_new->type)
    {
        FunctionSet* fset;
        fset = &f_new->info.set.funcs;
        GrowArray( Function, *fset, 1 );
        f_new = ARefLast( Function, *fset );
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
    TypeInfo* info;
    pkey_t typei;
    typei = Named_Types.n;
    GrowArray( TypeInfo, Named_Types, 1 );
    info = ARefLast( TypeInfo, Named_Types );
    if (name)  info->name = MemDup( char, name, 1+strlen(name) );
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
    for (i = 0; i < Named_Types.n; ++i)
    {
        const char* str;
        str = ARef(TypeInfo, Named_Types, i)->name;
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
    dst = ARef( TypeInfo, Named_Types, type );

    f.nargs = src->nmembs;
    f.types = src->types;
    f.type = ConstructFunc;
    f.info.construct.type = type;
    add_named_function (src->name, &f);

    dst->nmembs = src->nmembs;
    dst->types  = MemDup(pkey_t, src->types, src->nmembs);
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
    dst = ARef( TypeInfo, Named_Types, type );

    dst->nmembs = src->nmembs;
    set_simple_type_P (dst, 0);
    dst->types  = MemDup(pkey_t, src->types, src->nmembs);
    
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
    info = ARef( TypeInfo, Named_Types, typei );
    info->nmembs = Internal_Types.n;
    set_simple_type_P (info, 0);
    info->types = 0;
    PushStack( InternalTypeInfo, Internal_Types, iinfo );
    assert (internal_type_P (info));
    return typei;
}

static pkey_t find_named_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Types.n; ++i)
    {
        const char* str;
        str = ARef(TypeInfo, Named_Types, i)->name;
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
    PushStack( Pair, run->e, &expr );
}

static unsigned parse_list (Array* arr, char* str)
{
    unsigned i = 1;
    unsigned nmemb = 0;  /* #args + 1 */
    unsigned diff = 1; /* Re-used state. */
    unsigned toki; /* Current token index. */

    if (str[0] != '(')  return 0;
    str[0] = 0;

    toki = arr->n;
    GrowArray( Pair, *arr, 1 );

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
            diff = parse_list (arr, &str[i]);
            if (!diff)  break;
            i += diff;
        }
        else
        {
            if (diff)
            {
                Pair* tok;
                ++ nmemb;
                diff = 0;
                GrowArray( Pair, *arr, 1 );
                tok = ARefLast( Pair, *arr );
                tok->key = CStringInternalType;
                tok->val = &str[i];
            }
            ++ i;
        }
    }

    if (diff)
    {
        Pair* fntok = ARef( Pair, *arr, toki );
        fntok->key = nmemb;
        set_funcall_P (fntok, 1);
        fntok->val = (void*) (arr->n - (size_t) fntok->val);
    }
    else
    {
            /* If there was a failure, revert parse tree. */
        arr->n = toki;
    }
    return diff;
}


static pkey_t interp_deftype (const char* str)
{
    unsigned i;
    pkey_t typei;
    TypeInfo info;
    Array types;
    Pair* node;
    Array parsed;
    char* buf;
    buf = MemDup( char, str, 1+ strlen (str) );

    InitArray( Pair, parsed, 1 );
    InitArray( Pair, types, 1 );
    
    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");
    assert (!str[i]);

    assert (parsed.n > 1);

    node = ARef( Pair, parsed, 0 );
    assert (funcallP (node) && "Plain value at toplevel?!");

    node = ARef( Pair, parsed, 1 );
    assert (streqlP ("deftype", (char*)node->val));

    node = ARef( Pair, parsed, 2 );
    if (funcallP (node))
    {
        Array membs;
        InitArray( Pair, membs, 1 );

        node = ARef( Pair, parsed, 0 );
        assert (2 == StripPKey(node->key));

        node = ARef( Pair, parsed, 3 );

        info.name = (char*) node->val;

        for (i = 4; i < parsed.n; ++i)
        {
            const char* membstr;
            const char* typestr;
            node = ARef( Pair, parsed, i );
            if (funcallP (node))
            {
                unsigned nelems;
                nelems = StripPKey(node->key);
                assert (1 == nelems || 2 == nelems);

                node = ARef( Pair, parsed, ++i );
                assert (!funcallP (node));
                membstr = (char*) node->val;

                if (2 == nelems)
                {
                    node = ARef( Pair, parsed, ++i );
                    typestr = (char*) node->val;
                }
                else
                {
                    typestr = "nil";
                }
            }
            else
            {
                membstr = (char*) node->val;
                typestr = "any";
            }

            dPushStack( const char*, membs, membstr );
            dPushStack( pkey_t, types, ensure_named_type (typestr) );
        }

        assert (membs.n == types.n);
        info.nmembs = types.n;
        info.types = (pkey_t*) types.a;

        typei = add_simple_type (&info, (const char**) membs.a);

        free (membs.a);
    }
    else
    {
        info.name = (char*) node->val;

        for (i = 3; i < parsed.n; ++i)
        {
            const char* typestr;
            node = ARef( Pair, parsed, i );
            assert (!funcallP (node));
            typestr = (char*) node->val;
            dPushStack( pkey_t, types, ensure_named_type (typestr) );
        }

        if (3 == parsed.n)
        {
            const TypeInfo* chkinfo;
            typei = find_named_type (info.name);
            chkinfo = type_info (typei);
            assert (internal_type_P (chkinfo));
        }
        else
        {
            info.nmembs = types.n;
            info.types = (pkey_t*) types.a;
            typei = add_compound_type (&info);
        }
    }

    free (parsed.a);
    free (types.a);
    free (buf);
    return typei;
}

static void interp_def (const char* str)
{
    const unsigned formals_offset = 4;
    char* funcname;
    unsigned i;
    Function func;
    Array parsed, types, formals, exprs, argmap;
    Pair* node;
    char* buf;
    buf = MemDup( char, str, 1+ strlen (str) );

    InitArray( Pair,     parsed,  1 );
    InitArray( Pair,     exprs,   1 );
    InitArray( unsigned, argmap,  1 );
    
    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");

    assert (parsed.n > 1);

    node = ARef( Pair, parsed, 0 );
    assert (funcallP (node));
    assert (2 == StripPKey(node->key) || 3 == StripPKey(node->key));

    node = ARef( Pair, parsed, 1 );
    assert (streqlP ("def", (char*) node->val));

    node = ARef( Pair, parsed, 2 );
    assert (funcallP (node) && "Non-functions not supported yet in def's.");
    func.nargs = StripPKey(node->key);
    assert (func.nargs > 0);
    -- func.nargs;

    InitArray( pkey_t, types,   func.nargs );
    InitArray( char*,  formals, func.nargs );

    node = ARef( Pair, parsed, 3 );
    assert (!funcallP (node));
    funcname = (char*) node->val;

    func.type = StandardFunc;
        /* TODO: macros */
        /* func.type = ('\'' == funcname[0]) ? MacroFunc : StandardFunc; */

        /* TODO: macros */
    if (macro_func_P (&func))
        assert (1 == func.nargs && "Macros only take one list argument.");

    for (i = formals_offset; types.n < func.nargs; ++i)
    {
        const char* typestr;
        char* formalstr;
        node = ARef( Pair, parsed, i );
        
            /* TODO: macros */
        if (macro_func_P (&func))
            assert (!funcallP (node) && "Use implied macro param type.");

        if (funcallP (node))
        {
            unsigned nelems;
            nelems = StripPKey(node->key);
            assert (1 == nelems || 2 == nelems);

            node = ARef( Pair, parsed, ++i );
            assert (!funcallP (node) && "(def ((name) arg1 arg2)) ?!");
            formalstr = (char*) node->val;

            if (2 == nelems)
            {
                node = ARef( Pair, parsed, ++i );
                typestr = (char*) node->val;
            }
            else
            {
                typestr = "nil";
            }
        }
        else
        {
            typestr = "any";
            formalstr = (char*) node->val;
        }

        dPushStack( pkey_t, types, find_named_type (typestr) );
        dPushStack( char*, formals, formalstr );
    }

    for (; i < parsed.n; ++i)
    {
        unsigned argi;
        const char* symname;
        Pair expr;

        node = ARef( Pair, parsed, i );
        if (funcallP (node))
        {
            expr.key = StripPKey(node->key);
            assert (expr.key > 0);
            expr.key = (expr.key - 1);
            set_funcall_P (&expr, 1);

            node = ARef( Pair, parsed, ++i );
        }
        else
        {
            expr.key = 0;
        }

        assert (!funcallP (node));
        symname = (char*) node->val;

        for (argi = 0; argi < formals.n; ++argi)
            if (streqlP (symname, dARef( char*, formals, argi )))
                break;

        if (argi < formals.n)
        {
            dPushStack( unsigned, argmap, exprs.n );
            dPushStack( unsigned, argmap, argi );
        }
        else
        {
            expr.val = ensure_named_function ((char*) node->val);
            assert (expr.val && "Function not found.");
        }

        PushStack( Pair, exprs, &expr );
    }

    if (0 == exprs.n)
    {
        Pair expr;
        expr.key = 0;
        set_funcall_P (&expr, 1);
        expr.val = find_named_function ("nil");
        assert (expr.val && "Function not found.");
        PushStack( Pair, exprs, &expr );
    }

    if (StandardFunc == func.type)
    {
        func.types = (pkey_t*) types.a;
        func.info.std.nexprs = exprs.n;
        func.info.std.nsubst = argmap.n / 2;
        func.info.std.exprs = (Pair*) exprs.a;
        func.info.std.argmap = (unsigned*) argmap.a;
    }
    add_named_function (funcname, &func);

    free (parsed.a);
    if (func.nargs > 0)
    {
            /* free (types.a); */
        free (formals.a);
    }
    cleanup_Function (&func);
    /*
    free (exprs.a);
    free (argmap.a);
    */
    free (buf);
}

static unsigned parsed_to_sexpr (Pair* expr, const Array* parsed, unsigned i)
{
    Pair* node;
    unsigned elemi, nelems;
    assert (i < parsed->n && "ProgErr, overrunning sexpr parse.");
    node = ARef( Pair, *parsed, i++ );
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

static unsigned eval_macro (Runtime* run, const Array* parsed, unsigned i)
{
    Pair* expr;
    unsigned nargs;
    assert (run->e.n && "Nothing in expression stack.");
    expr = ARefLast( Pair, run->e );
    assert (funcallP (expr) && "No function call atop expression stack.");
    nargs = StripPKey(expr->key);
    while (nargs)
    {
        Pair* expr;
        GrowArray( Pair, run->e, 1 );
        expr = ARefLast( Pair, run->e );
        i = parsed_to_sexpr (expr, parsed, i);
        -- nargs;
    }
    eval1func (run);
    expr = PopStack( Pair, run->d );
    PushStack( Pair, run->e, expr );
    return i;
}

static void parse_to_runtime (Runtime* run, const char* str)
{
    unsigned i;
    Array parsed;
    const unsigned N = 1;
    char* buf;
    buf = AllocT( char, 1+ strlen (str) );
    strcpy (buf, str);

    InitArray( Pair, run->d, N );
    InitArray( Pair, run->e, N );
    InitArray( Pair, parsed, N );

    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");

    for (i = 0; i < parsed.n; ++i)
    {
        Pair* node;
        node = ARef( Pair, parsed, i );
        if (funcallP (node))
        {
            unsigned nargs;
            ++i;
            nargs = StripPKey(node->key);
            assert (nargs);
            -- nargs;

            node = ARef( Pair, parsed, i );
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
            PushStack( Pair, run->e, &pair );
        }
    }
    free (parsed.a);
    free (buf);
}

static void cleanup_runtime (Runtime* run)
{
    CleanupArray( Pair, run->d );
    CleanupArray( Pair, run->e );
}

static void interp_eval (FILE* out, const char* str)
{
    Runtime stacked_run;
    Runtime* run;
    run = &stacked_run;

    parse_to_runtime (run, str);

    eval (run);
    write_Pair (out, ARef(Pair, run->d, 0));
    fputs ("\n", out);

    cleanup_runtime (run);
}

static void assert_eql (const char* lhs, const char* rhs)
{
    Pair expr;
    Runtime stacked_lhsrun;
    Runtime stacked_rhsrun;
    Runtime* lhsrun;
    Runtime* rhsrun;
    lhsrun = &stacked_lhsrun;
    rhsrun = &stacked_rhsrun;

    parse_to_runtime (lhsrun, lhs);
    parse_to_runtime (rhsrun, rhs);

    eval (lhsrun);
    eval (rhsrun);

    if (lhsrun->e.n < 3)
        GrowArray(Pair, lhsrun->e, 3 - lhsrun->e.n);

    expr.key = 2;
    set_funcall_P (&expr, 1);
    expr.val = find_named_function ("eql");
    assert (expr.val && "Function not found.");
    copy_Pair (ARef( Pair, lhsrun->e, 0 ), &expr);
    copy_Pair (ARef( Pair, lhsrun->e, 1 ), ARef( Pair, rhsrun->d, 0 ));
    copy_Pair (ARef( Pair, lhsrun->e, 2 ), ARef( Pair, lhsrun->d, 0 ));
    ClearArray( Pair, rhsrun->d );
    ClearArray( Pair, lhsrun->d );
    eval (lhsrun);

    copy_Pair (&expr, ARef( Pair, lhsrun->d, 0 ));
    assert (StripPKey(expr.key) == find_named_type ("yes")
            && "Evaluated expressions are not equal! lhs != rhs.");

    cleanup_runtime (lhsrun);
    cleanup_runtime (rhsrun);
}


static void test_cases (FILE* out)
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

static void write_int_fn (FILE* out, const void* val)
{
    int i;
    i = PtrTo(int, val);
    fprintf (out, "('int %d)", i);
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
    const unsigned N = 1;
    pkey_t typei;
    InitArray( TypeInfo, Named_Types, N );
    InitArray( InternalTypeInfo, Internal_Types, N );
    InitArray( NamedFunction, Named_Functions, N );

    {
            /* Add the /any/ type, it's hardcoded. */
        TypeInfo* info;
        typei = ensure_named_type ("any");
        info = ARef( TypeInfo, Named_Types, typei );
        info->nmembs = 0;
        set_simple_type_P (info, 0);
        assert (AnyType == typei);
    }

    {   /* Add internal types. */
        InternalTypeInfo internal;

        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn =
            (void (*) (FILE*, const void*)) &write_Function;
        typei = add_internal_type ("func", &internal);
        assert (FunctionInternalType == typei);

        internal.write_fn = 0;
        typei = add_internal_type ("'", &internal);
        assert (VarArgInternalType == typei);

        internal.write_fn =
            (void (*) (FILE*, const void*)) &write_CString;
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
    CleanupArray( NamedFunction, Named_Functions );
    CleanupArray( TypeInfo, Named_Types );
    free (Internal_Types.a);
}

int main ()
{
    FILE* out;
    out = stdout;
    init_lisp ();

    interp_deftype ("(deftype bool yes nil)");

    interp_def ("(def (or (a yes) (b yes)) (yes))");
    interp_def ("(def (or (a yes) (b    )) (yes))");
    interp_def ("(def (or (a    ) (b yes)) (yes))");
    interp_def ("(def (or (a    ) (b    ))      )");

    interp_def ("(def (and (a yes) (b yes)) (yes))");
    interp_def ("(def (and (a yes) (b    ))      )");
    interp_def ("(def (and (a    ) (b yes))      )");
    interp_def ("(def (and (a    ) (b    ))      )");

    interp_def ("(def (impl (a yes) (b yes)) (yes))");
    interp_def ("(def (impl (a yes) (b    ))      )");
    interp_def ("(def (impl (a    ) (b yes)) (yes))");
    interp_def ("(def (impl (a    ) (b    )) (yes))");

    interp_def ("(def (eql (a yes) (b yes)) (yes))");
    interp_def ("(def (eql (a yes) (b    ))      )");
    interp_def ("(def (eql (a    ) (b yes))      )");
    interp_def ("(def (eql (a    ) (b    )) (yes))");

    interp_def ("(def (not (a    )) (yes))");
    interp_def ("(def (not (a yes))      )");

    interp_def ("(def (if (a    ) b c) c)");
    interp_def ("(def (if (a yes) b c) b)");

    interp_def ("(def (eql (a cons) (b     )))");
    interp_def ("(def (eql (a     ) (b cons)))");
    interp_def ("(def (eql (a cons) (b cons))"
                "  (and (eql (car a) (car b))"
                "       (eql (cdr a) (cdr b))))");

    interp_def ("(def (cat (a     ) (b list)) b)");
    interp_def ("(def (cat (a cons) (b list))"
                "  (cons (car a)"
                "        (cat (cdr a) b)))");

    interp_def ("(def (list a) (cons a (nil)))");

    interp_def ("(def (rev (L)))");
    interp_def ("(def (rev (L cons))"
                "  (cat (rev (cdr L))"
                "       (list (car L))))");

    interp_def ("(def (map (f func) (L)))");
    interp_def ("(def (map (f func) (L cons))"
                "  (cons (f (car L))"
                "         (map f (cdr L))))");

    interp_def ("(def (consif (pred func) e L)"
                "  (if (pred e) (cons e L) L))");

    interp_def ("(def (filter (f func) (L)))");
    interp_def ("(def (filter (f func) (L cons))"
                "  (consif f (car L) (filter f (cdr L))))");

    interp_deftype ("(deftype (set (elements list)))");

    interp_def ("(def (in e (L)))");
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
    interp_def ("(def (zero (a nonzero-int)))");

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
    cleanup_lisp ();
    return 0;
}

