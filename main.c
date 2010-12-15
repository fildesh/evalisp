
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
static const pkey_t FunctionInternalType = 0;
static const pkey_t AnyType = 1;

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
    MultiFunc,
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
    FunctionSet a; /* Array of functions. */
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
    void (** get_fns) (Pair*, unsigned, void*);
};
typedef struct internal_type_info_struct InternalTypeInfo;

static const TypeInfo* type_info (pkey_t type)
{
    assert (type < Named_Types.n);
    return ARef( TypeInfo, Named_Types, type );
}

static const InternalTypeInfo* internal_type_info (pkey_t type)
{
    assert (type < Internal_Types.n);
    return ARef( InternalTypeInfo, Internal_Types, type );
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
    if (CALLBIT & pair->key)
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
    if (type < Internal_Types.n)
    {
        const InternalTypeInfo* info;

        info = internal_type_info (type);
        if (info->copy_fn)
        {
            dst->key = MUTABIT & src->key;
            dst->val = (*info->copy_fn) (src->val);
        }
        else
        {
            assert (!(MUTABIT & src->key));
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
            assert (!(MUTABIT & src->key));
            set_pair (dst, src);
        }
        else
        {
            unsigned i;
            dst->key = MUTABIT | type;
            dst->val = malloc (info->nmembs * sizeof(Pair));

            src = (Pair*) src->val;
            dst = (Pair*) dst->val;
            for (i = 0; i < info->nmembs; ++i)
                copy_Pair (&dst[i], &src[i]);
        }
    }
}

static
    int
typeofp (pkey_t a, pkey_t t)
{
    TypeInfo* info;
    info = ARef( TypeInfo, Named_Types, a );
    assert (info->nmembs == StripWildBit(info->nmembs));

    if (AnyType == t)  return 1;

    info = ARef( TypeInfo, Named_Types, t );
    if (WILDBIT & info->nmembs)
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
            if (!typeofp (StripPKey(args[j].key), func->types[j]))
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

    if (CALLBIT & expr->key)
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
                if (!(CALLBIT & esk[dst_idx].key))
                    esk[dst_idx].key = dsk[src_idx].key;
                esk[dst_idx].val = dsk[src_idx].val;
            }
                /* Handle mutable arguments. */
            for (i = 0; i < f->nargs; ++i)
            {
                unsigned j, min_dst;
                if (!(MUTABIT & dsk[i].key))  continue;
                min_dst = nexprs;
                for (j = 0; j < nsubst; ++j)
                {
                    unsigned dst_idx;
                    if (i != argmap[2*j+1])  continue;
                    dst_idx = argmap[2*j];
                    if (dst_idx < min_dst)  min_dst = dst_idx;
                    esk[dst_idx].key &= ~MUTABIT;
                }
                if (min_dst == nexprs)
                    cleanup_Pair (&dsk[i]);
                else
                    esk[min_dst].key |= MUTABIT;
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
                val = (Pair*) malloc (f->nargs * sizeof (Pair));
                    /* This is a function to construct a type. */
                for (i = 0; i < f->nargs; ++i)
                {
                    if (MUTABIT & dsk[i].key)
                        set_pair (&val[i], &dsk[i]);
                    else
                        copy_Pair (&val[i], &dsk[i]);
                }
                dsk[0].key = MUTABIT | f->info.construct.type;
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

            if (MUTABIT & tmp.key)
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
        if (0 == strcmp (fs->name, name))
        {
            return &fs->a;
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

static void copy_TypeInfo (TypeInfo* dst, const TypeInfo* src)
{
    dst->name   = MemDup( char, src->name, 1+strlen(src->name) );
    dst->nmembs = src->nmembs;
    dst->types  = MemDup( pkey_t, src->types, StripWildBit(src->nmembs) );
}

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
    CleanupArray( Function, set->a );
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

static void force_init_named_function (const char* name)
{
    NamedFunctionSet set;
    set.name = MemDup(char, name, 1+strlen(name));
    InitArray(Function, set.a, 1);
    PushStack(NamedFunctionSet, Named_Functions, &set);
}

static void init_named_function (const char* name)
{
    FunctionSet* fs;
    fs = find_named_function (name);
    if (!fs)  force_init_named_function (name);
}

static Function* add_named_function (const char* name, const Function* f)
{
    FunctionSet* fs;
    Function* f_new;
    fs = find_named_function (name);
    if (!fs)
    {
        force_init_named_function (name);
        fs = &ARefLast( NamedFunctionSet, Named_Functions )->a;
    }
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
        if (0 == strcmp (ARef(TypeInfo, Named_Types, i)->name, name))
            return i;

    GrowArray( TypeInfo, Named_Types, 1 );
    info = ARefLast( TypeInfo, Named_Types );
    info->name = MemDup( char, name, 1+strlen(name) );
    info->nmembs = WILDBIT;
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
    assert (WILDBIT == dst->nmembs);

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

    return type;
}

static pkey_t add_compound_type (const TypeInfo* src)
{
    pkey_t type;
    TypeInfo* dst;

    type = ensure_named_type (src->name);
    dst = ARef( TypeInfo, Named_Types, type );
    assert (WILDBIT == dst->nmembs);

    dst->nmembs = WILDBIT | src->nmembs;
    dst->types  = MemDup(pkey_t, src->types, src->nmembs);
    
    return type;
}

static pkey_t find_named_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Named_Types.n; ++i)
        if (0 == strcmp (ARef(TypeInfo, Named_Types, i)->name, name))
            return i;
    assert (0 && "Unknown type.");
}

static void push_function (Runtime* run, const char* name, pkey_t nargs)
{
    Pair pair;

    pair.key = CALLBIT | nargs;
    pair.val = find_named_function (name);
    PushStack( Pair, run->e, &pair );
}

static void init_lisp ()
{
    const unsigned N = 1;
    InitArray( TypeInfo, Named_Types, N );
    InitArray( InternalTypeInfo, Internal_Types, N );
    InitArray( NamedFunctionSet, Named_Functions, N );

    {   /* Add internal types. */
        TypeInfo info;
        InternalTypeInfo internal;

        info.name = "func";
        info.nmembs = 0;
        info.types = 0;

            /* internal.copy_fn = copy_FunctionSet; */
            /* internal.cleanup_fn = cleanup_FunctionSet; */
        internal.copy_fn = 0;
        internal.free_fn = 0;
        internal.write_fn =
            (void (*) (FILE*, const void*)) &write_FunctionSet;
        add_simple_type (&info, 0);
        PushStack( InternalTypeInfo, Internal_Types, &internal );
    }

    {
            /* Add the /any/ type, it's hardcoded. */
        pkey_t t;
        TypeInfo ts;
        ts.name = "any";
        ts.nmembs = 0;
        t = add_compound_type (&ts);
        assert (AnyType == t);
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
        fntok->key = CALLBIT | nmemb;
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
    char* buf = malloc ((1+ strlen (str)) * sizeof(char));
    strcpy (buf, str);

    InitArray( Pair, parsed, 1 );
    InitArray( Pair, types, 1 );
    
    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");
    assert (!str[i]);

    assert (parsed.n > 1);

    node = ARef( Pair, parsed, 0 );
    assert (CALLBIT & node->key);

    node = ARef( Pair, parsed, 1 );
    assert (!strcmp ("deftype", (char*)node->val));

    node = ARef( Pair, parsed, 2 );
    if (CALLBIT & node->key)
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
            if (CALLBIT & node->key)
            {
                unsigned nelems;
                nelems = StripPKey(node->key);
                assert (1 == nelems || 2 == nelems);

                node = ARef( Pair, parsed, ++i );
                assert (!(CALLBIT & node->key));
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
            assert (!(CALLBIT & node->key));
            typestr = (char*) node->val;
            dPushStack( pkey_t, types, ensure_named_type (typestr) );
        }

        info.nmembs = types.n;
        info.types = types.a;
        add_compound_type (&info);
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
    char* buf = malloc ((1+ strlen (str)) * sizeof(char));
    strcpy (buf, str);

    InitArray( Pair,     parsed,  1 );
    InitArray( Pair,     exprs,   1 );
    InitArray( unsigned, argmap,  1 );
    
    i = parse_list (&parsed, buf);
    assert (i && "Parse failed.");

    assert (parsed.n > 1);

    node = ARef( Pair, parsed, 0 );
    assert (CALLBIT & node->key);
    assert (2 == StripPKey(node->key) || 3 == StripPKey(node->key));

    node = ARef( Pair, parsed, 1 );
    assert (!strcmp ("def", (char*) node->val));

    node = ARef( Pair, parsed, 2 );
        /* Don't support variable assignment yet.
         * Need more levels of scoping.
         */
    assert (CALLBIT & node->key);
    func.nargs = StripPKey(node->key);
    assert (func.nargs > 0);
    -- func.nargs;

    if (func.nargs > 0)
    {
        InitArray( pkey_t, types,   func.nargs );
        InitArray( char*,  formals, func.nargs );
    }

    node = ARef( Pair, parsed, 3 );
    assert (!(CALLBIT & node->key));
    funcname = (char*) node->val;

    for (i = formals_offset; types.n < func.nargs; ++i)
    {
        const char* typestr;
        char* formalstr;
        node = ARef( Pair, parsed, i );
        if (CALLBIT & node->key)
        {
            unsigned nelems;
            nelems = StripPKey(node->key);
            assert (1 == nelems || 2 == nelems);

            node = ARef( Pair, parsed, ++i );
            assert (!(CALLBIT & node->key));
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
        if (CALLBIT & node->key)
        {
            expr.key = StripPKey(node->key);
            assert (expr.key > 0);
            expr.key = CALLBIT | (expr.key - 1);

            node = ARef( Pair, parsed, ++i );
        }
        else
        {
            expr.key = 0;
        }

        assert (!(CALLBIT & node->key));
        symname = (char*) node->val;

        for (argi = 0; argi < formals.n; ++argi)
            if (0 == strcmp (symname, dARef( char*, formals, argi )))
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
        expr.key = CALLBIT | 0;
        expr.val = find_named_function ("nil");
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
    char* buf = malloc ((1+ strlen (str)) * sizeof(char));
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
        if (CALLBIT & node->key)
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

    expr.key = CALLBIT | 2;
    expr.val = find_named_function ("eql");
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
                "(map not (cons (yes) (cons (nil) (cons (yes) (nil))))))");

    assert_eql ("(list (yes))",
                "(car (list (list (yes)))))");

    assert_eql ("(cons (nil) (list (yes)))",
                "(rev (cons (yes) (cons (nil) (nil)))))");
}


int main ()
{
    FILE* out;
    out = stdout;
    init_lisp ();

    interp_deftype ("(deftype (nil))");
    interp_deftype ("(deftype (yes))");
    interp_deftype ("(deftype (cons car (cdr list)))");

    interp_deftype ("(deftype list cons nil)");
    interp_deftype ("(deftype bool yes nil)");

        /* Since pointers to /Named_Functions/ members are used,
         * don't resize the array after this block.
         */
    init_named_function ("and");
    init_named_function ("or");
    init_named_function ("impl");
    init_named_function ("eql");
    init_named_function ("not");
    init_named_function ("list");
    init_named_function ("cat");
    init_named_function ("rev");
    init_named_function ("map");

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

    cleanup_lisp ();
    return 0;
}

