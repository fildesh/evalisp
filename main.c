
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
    /* static const char* NilTypeName = "nil"; */
    /* static const char* AnyTypeName = "any"; */
static pkey_t ScratchPKey;
static const pkey_t AnyType = 0;
static const pkey_t FunctionInternalType = 1;

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
    PendingDefFunc, SetOfFunc,
    NFuncTypes
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
            void (* f) (Pair*);
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
        } multi;
    } info;
};
typedef struct function_struct Function;

struct named_function_set_struct
{
    char* name;
    FunctionSet* a; /* Array of functions. */
};
typedef struct named_function_set_struct NamedFunctionSet;

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

static const TypeInfo* type_info (pkey_t type)
{
    assert (type < Named_Types.n);
    return ARef( TypeInfo, Named_Types, type );
}

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

static int simple_type_P (const TypeInfo* info)
{
    return !(WILDBIT & info->nmembs);
}

static void set_simple_type_P (TypeInfo* info, int b)
{
    if (b)  info->nmembs &= WILDBIT;
    else    info->nmembs |= WILDBIT;
}

static int compound_type_P (pkey_t typei)
{
    TypeInfo* info;
    info = ARef( TypeInfo, Named_Types, typei );
    return !simple_type_P (info) && info->types;
}

static int internal_type_P (pkey_t typei)
{
    TypeInfo* info;
    info = ARef( TypeInfo, Named_Types, typei );
    return !simple_type_P (info) && !info->types;
}

static const InternalTypeInfo* internal_type_info (pkey_t typei)
{
    TypeInfo* info;
    unsigned i;
    assert (internal_type_P (typei));
    info = ARef( TypeInfo, Named_Types, typei );
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
write_Pair (FILE* out, const Pair* pair)
{
    pkey_t type;
    if (funcallP (pair))
        type = FunctionInternalType;
    else
        type = StripPKey(pair->key);
    assert (type < Named_Types.n);
    if (type < Internal_Types.n)
    {
        const InternalTypeInfo* info;
        info = internal_type_info (type);
        assert (info->write_fn);
        (*info->write_fn) (out, pair->val);
    }
    else
    {
        unsigned i;
        const TypeInfo* info;
        info = type_info (type);

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
write_Function (FILE* out, const Function* f, const char* name)
{
    unsigned i;
    fprintf (out, "(%s", name);
    for (i = 0; i < f->nargs; ++i)
    {
        pkey_t t;
        fputc (' ', out);
        t = f->types[f->nargs -i -1];
        fputs (ARef( TypeInfo, Named_Types, t )->name, out);
    }
    fputc (')', out);
}

static
    void
write_FunctionSet (FILE* out, const FunctionSet* fs)
{
    unsigned i;
    const char* func;

    {
            /* Begin hacks. */
        NamedFunctionSet set;
        size_t offset;
        offset = (size_t) &set.a - (size_t) &set;
        func = ((NamedFunctionSet*) ((size_t)fs - offset))->name;
            /* End hacks. */
    }

    fputs ("(func", out);
    for (i = 0; i < fs->n; ++i)
    {
        fputc (' ', out);
        write_Function (out, ARef( Function, *fs, i ), func);
    }
    fputc (')', out);
}

static
    void
cleanup_Pair (Pair* pair)
{
    pkey_t type;
    type = StripPKey(pair->key);
    assert (type < Named_Types.n);
    if (type < Internal_Types.n)
    {
        const InternalTypeInfo* info;
        info = internal_type_info (type);
        if (info->free_fn)
            (*info->free_fn) (pair->val);
        else
            assert (!info->copy_fn);
    }
    else
    {
        const TypeInfo* info;
        info = type_info (type);
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
    pkey_t type;
    type = StripPKey(src->key);
    assert (type < Named_Types.n);
    if (internal_type_P (type))
    {
        const InternalTypeInfo* info;

        info = internal_type_info (type);
        if (info->copy_fn)
        {
            dst->key = mutableP (src);
            dst->val = (*info->copy_fn) (src->val);
        }
        else
        {
            assert (!mutableP (src));
            assert (!info->free_fn);
            set_pair (dst, src);
        }
    }
    else
    {
        const TypeInfo* info;
        info = type_info (type);
        if (!info->nmembs)
        {
            assert (!mutableP (src));
            set_pair (dst, src);
        }
        else
        {
            unsigned i;
            dst->key = MUTABIT | type;
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
    TypeInfo* info;
    assert (!compound_type_P (a)
            && "Why check for compound type 'is a' compound type?");

    if (AnyType == t)  return 1;

    info = ARef( TypeInfo, Named_Types, t );
    if (compound_type_P (t))
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
    const Function*
find_function (unsigned nargs, const Pair* args, const FunctionSet* fset)
{
    unsigned i;
    for (i = 0; i < fset->n; ++i)
    {
        const Function* func;
        unsigned j;
        func = ARef(Function, *fset, i);
        if (nargs != func->nargs)
            continue;
        for (j = 0; j < nargs; ++j)
            if (!typeofP (StripPKey(args[j].key), func->types[j]))
                break;
        if (j == nargs)
            return func;
    }
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

        f = find_function (nargs, dsk, (FunctionSet*) expr->val);
        if (!f) {
            FILE* out;
            out = stderr;

            fputs ("Data stack:\n", out);
            GrowArray( Pair, run->d, nargs );
            for (i = 0; i < run->d.n; ++i)
            {
                write_Pair (out, ARef(Pair, run->d, i));
                fputc ('\n', out);
            }
            fputs ("Expression stack:\n", out);
            for (i = 0; i < run->e.n; ++i)
            {
                write_Pair (out, ARef(Pair, run->e, i));
                fputc ('\n', out);
            }
            fputs ("Current function:\n", out);
            write_Pair (out, expr);
            fprintf (out, "\nnargs: %u\n", nargs);
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
            (f->info.internal.f) (dsk);
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
            assert(0);
        }
    }
    else
    {
        PushStack (Pair, run->d, expr);
    }
}

static void eval (Runtime* run)
{
    while (run->e.n)  eval1 (run);
    assert (1 == run->d.n);
}

static FunctionSet* find_named_function (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Functions.n; ++i)
    {
        NamedFunctionSet* fs;
        fs = ARef(NamedFunctionSet, Named_Functions, i);
        if (streqlP (fs->name, name))
        {
            return fs->a;
        }
    }
    return 0;
}

static void copy_Function (Function* dst, const Function* src)
{
    memcpy (dst, src, sizeof (Function));
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
    if (f->nargs)
        free (f->types);
    if (StandardFunc == f->type)
    {
        free (f->info.std.exprs);
        free (f->info.std.argmap);
    }
}

static void cleanup_NamedFunctionSet (NamedFunctionSet* set)
{
    free (set->name);
    CleanupArray( Function, *set->a );
    free (set->a);
}

static void cleanup_TypeInfo (TypeInfo* info)
{
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

static FunctionSet* force_init_named_function (const char* name)
{
    NamedFunctionSet set;
    set.name = MemDup(char, name, 1+strlen(name));
    set.a = AllocT( FunctionSet, 1 );
    InitArray(Function, *set.a, 1);
    PushStack(NamedFunctionSet, Named_Functions, &set);
    return ARefLast( NamedFunctionSet, Named_Functions )->a;
}

static FunctionSet* ensure_named_function (const char* name)
{
    FunctionSet* fs;
    fs = find_named_function (name);
    if (!fs)  fs = force_init_named_function (name);
    return fs;
}

static Function* add_named_function (const char* name, const Function* f)
{
    FunctionSet* fs;
    Function* f_new;
    fs = ensure_named_function (name);

    GrowArray(Function, *fs, 1);
    f_new = ARefLast( Function, *fs );
    copy_Function (f_new, f);
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

static pkey_t ensure_named_type (const char* name)
{
    unsigned i;
    TypeInfo* info;
    for (i = 0; i < Named_Types.n; ++i)
        if (streqlP (ARef(TypeInfo, Named_Types, i)->name, name))
            return i;

    GrowArray( TypeInfo, Named_Types, 1 );
    info = ARefLast( TypeInfo, Named_Types );
    info->name = MemDup( char, name, 1+strlen(name) );
    info->nmembs = 0;
    set_simple_type_P (info, 0);
    info->types = &ScratchPKey;
    return i;
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

    assert (!compound_type_P (type) && !internal_type_P (type));
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
    
    assert (compound_type_P (type));
    return type;
}

static
    pkey_t
add_internal_type (const char* name, const InternalTypeInfo* iinfo)
{
    pkey_t typei;
    TypeInfo* info;
    typei = ensure_named_type (name);
    info = ARef( TypeInfo, Named_Types, typei );
    info->nmembs = Internal_Types.n;
    set_simple_type_P (info, 0);
    info->types = 0;
    PushStack( InternalTypeInfo, Internal_Types, iinfo );
    assert (internal_type_P (typei));
    return typei;
}

static pkey_t find_named_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Types.n; ++i)
        if (streqlP (ARef(TypeInfo, Named_Types, i)->name, name))
            return i;
    assert (0 && "Unknown type.");
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

static void init_lisp ()
{
    const unsigned N = 1;
    InitArray( TypeInfo, Named_Types, N );
    InitArray( InternalTypeInfo, Internal_Types, N );
    InitArray( NamedFunctionSet, Named_Functions, N );

    {
            /* Add the /any/ type, it's hardcoded. */
        pkey_t typei;
        TypeInfo* info;
        typei = ensure_named_type ("any");
        info = ARef( TypeInfo, Named_Types, typei );
        info->nmembs = 0;
        set_simple_type_P (info, 0);
        assert (AnyType == typei);
    }

    {   /* Add internal types. */
        InternalTypeInfo internal;

            /* internal.copy_fn = copy_FunctionSet; */
            /* internal.cleanup_fn = cleanup_FunctionSet; */
        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn =
            (void (*) (FILE*, const void*)) &write_FunctionSet;
        add_internal_type ("func", &internal);
    }
}

static void cleanup_lisp ()
{
    CleanupArray( NamedFunctionSet, Named_Functions );
    CleanupArray( TypeInfo, Named_Types );
    free (Internal_Types.a);
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
                tok->key = 0;
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


static void interp_deftype (const char* str)
{
    unsigned i;
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

        add_simple_type (&info, (const char**) membs.a);

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
            assert (internal_type_P (find_named_type (info.name)));
        }
        else
        {
            info.nmembs = types.n;
            info.types = (pkey_t*) types.a;
            add_compound_type (&info);
        }
    }

    free (parsed.a);
    free (types.a);
    free (buf);
}

static void interp_def (const char* str)
{
    const unsigned formals_offset = 4;
    const char* funcname;
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
        /* Don't support variable assignment yet.
         * Need more levels of scoping.
         */
    assert (funcallP (node));
    func.nargs = StripPKey(node->key);
    assert (func.nargs > 0);
    -- func.nargs;

    if (func.nargs > 0)
    {
        InitArray( pkey_t, types,   func.nargs );
        InitArray( char*,  formals, func.nargs );
    }

    node = ARef( Pair, parsed, 3 );
    assert (!funcallP (node));
    funcname = (char*) node->val;

    for (i = formals_offset; types.n < func.nargs; ++i)
    {
        const char* typestr;
        char* formalstr;
        node = ARef( Pair, parsed, i );
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
            expr.val = find_named_function ((char*) node->val);
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

    func.types = (pkey_t*) types.a;
    func.type = StandardFunc;
    func.info.std.nexprs = exprs.n;
    func.info.std.nsubst = argmap.n / 2;
    func.info.std.exprs = (Pair*) exprs.a;
    func.info.std.argmap = (unsigned*) argmap.a;
    add_named_function (funcname, &func);

    free (parsed.a);
    if (func.nargs > 0)
    {
        free (types.a);
        free (formals.a);
    }
    free (exprs.a);
    free (argmap.a);
    free (buf);
}

static void parse_to_runtime (Runtime* run, const char* str)
{
    unsigned i;
    Array parsed;
    const unsigned N = 1;
    char* buf = AllocT( char, 1+ strlen (str) );
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
        }
        else
        {
            Pair pair;
                /* Assume it's a function for now. */
            pair.key = find_named_type ("func");
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
    assert (StripPKey(expr.key) == find_named_type ("yes"));

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
}


int main ()
{
    FILE* out;
    out = stdout;
    init_lisp ();

    {
        InternalTypeInfo internal;
        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn = 0;
        add_internal_type ("int", &internal);
        interp_deftype ("(deftype int)");
    }

    interp_deftype ("(deftype (nil))");
    interp_deftype ("(deftype (yes))");
    interp_deftype ("(deftype (cons car (cdr list)))");

    interp_deftype ("(deftype list cons nil)");
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

