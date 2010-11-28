
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "array.c"
static Array Internal_Types;
static Array Simple_Types;
static Array Compound_Types;
static Array Named_Functions;


typedef size_t pkey_t;

static const pkey_t MUTABIT = (pkey_t)1 << (8 * sizeof (pkey_t) -1);
static const pkey_t CALLBIT = (pkey_t)1 << (8 * sizeof (pkey_t) -2);
static const pkey_t AnyType = (pkey_t)1 << (8 * sizeof (pkey_t) -1);
static const pkey_t FunctionInternalType = 0;

#define StripPKey(k)  (k & ~(MUTABIT | CALLBIT))

struct pair_struct
{
    pkey_t key;
    void*  val;
};
typedef struct pair_struct Pair;

enum function_type_enum { StandardFunc, InternalFunc, ConstructFunc, AccessFunc, NFuncTypes };
typedef enum function_type_enum FunctionType;

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
    } info;
};
typedef struct function_struct Function;

typedef Array FunctionSet;

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

struct type_info_set_struct
{
    char* name;
    unsigned ntypes;
    pkey_t*   types;
};
typedef struct type_info_set_struct TypeInfoSet;

struct internal_type_info_struct
{
    void*  (* copy_fn) (const void*);
    void   (* free_fn) (void*);
    void  (* write_fn) (FILE*, const void*);
    void (** get_fns) (Pair*, unsigned, void*);
};
typedef struct internal_type_info_struct InternalTypeInfo;

static const TypeInfo* type_info (pkey_t type)
{
    assert (type == StripPKey( type ));
    assert (type < Simple_Types.n);
    return ARef( TypeInfo, Simple_Types, type );
}

static const InternalTypeInfo* internal_type_info (pkey_t type)
{
    assert (type == StripPKey( type ));
    assert (type < Internal_Types.n);
    return ARef( InternalTypeInfo, Internal_Types, type );
}

static
    unsigned
num_type_members (pkey_t type)
{
    return type_info (type) -> nmembs;
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
    assert (type < Simple_Types.n);
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
        t = f->types[i];
        if (AnyType & t)
        {
            t &= ~AnyType;
            fputs (ARef( TypeInfoSet, Compound_Types, t )->name, out);
        }
        else
        {
            fputs (ARef( TypeInfo, Simple_Types, t )->name, out);
        }
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
    assert (type < Simple_Types.n);
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
    assert (type < Simple_Types.n);
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
typeofsetp (pkey_t a, pkey_t ts)
{
    TypeInfoSet* set;
    unsigned i;
    if (!ts)  return 1;
    assert (ts < Compound_Types.n);
    set = ARef( TypeInfoSet, Compound_Types, ts );
    for (i = 0; i < set->ntypes; ++i)
        if (a == set->types[i])
            return 1;
    return 0;
}

static
    int
typeofp (pkey_t a, pkey_t t)
{
    if (AnyType & t)
        return typeofsetp (a, StripPKey(t));
    else
        return a == t;
}

static
    const Function*
find_function (unsigned nargs, const Pair* args, const FunctionSet* fset)
{
    unsigned i;
    for (i = 0; i < fset->N; ++i)
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

            /* Must have enough arguments. */
        assert (run->d.n >= nargs);

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

static
    void
eval (Runtime* run)
{
    while (run->e.n)  eval1 (run);
    assert (1 == run->d.n);
    write_Pair (stdout, ARef(Pair, run->d, 0));
    fputs ("\n", stdout);
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
    dst->types  = MemDup( pkey_t, src->types, src->nmembs );
}

static void copy_TypeInfoSet (TypeInfoSet* dst, const TypeInfoSet* src)
{
    dst->name   = MemDup( char, src->name, 1+strlen(src->name) );
    dst->ntypes = src->ntypes;
    dst->types  = MemDup( pkey_t, src->types, src->ntypes );
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
    if (info->nmembs)
        free (info->types);
}

static void cleanup_TypeInfoSet (TypeInfoSet* set)
{
    free (set->name);
    if (set->ntypes)
        free (set->types);
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

static pkey_t add_simple_type (const TypeInfo* info, const char* const* membs)
{
    unsigned i;
    Function f;
    pkey_t type;
    TypeInfo* info_new;

    type = Simple_Types.n;
    GrowArray( TypeInfo, Simple_Types, 1 );

    f.nargs = info->nmembs;
    f.types = info->types;
    f.type = ConstructFunc;
    f.info.construct.type = type;

    add_named_function (info->name, &f);
    info_new = ARef(TypeInfo, Simple_Types, type);
    copy_TypeInfo (info_new, info);
    reverse_types (info_new->nmembs, info_new->types);

    f.nargs = 1;
    f.type = AccessFunc;
    for (i = 0; i < info->nmembs; ++i)
    {
        f.types = &type;
        f.info.access.idx = info->nmembs - i - 1;
        add_named_function (membs[i], &f);
    }


    return type;
}

static pkey_t add_compound_type (const TypeInfoSet* set)
{
    pkey_t type;
    type = Compound_Types.n;
    GrowArray( TypeInfoSet, Compound_Types, 1 );
    copy_TypeInfoSet (ARef(TypeInfoSet, Compound_Types, type), set);
    return AnyType | type;
}

static pkey_t find_simple_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Simple_Types.n; ++i)
        if (0 == strcmp (ARef(TypeInfo, Simple_Types, i)->name, name))
            return i;
    assert (0 && "Unknown type.");
}

static pkey_t find_compound_type (const char* name)
{
    unsigned i;
    for (i = 0; i < Compound_Types.n; ++i)
        if (0 == strcmp (ARef(TypeInfoSet, Compound_Types, i)->name, name))
            return AnyType | i;
    assert (0 && "Unknown type.");
}

static void push_function (Runtime* run, const char* name, pkey_t nargs)
{
    Pair pair;

    pair.key = CALLBIT | nargs;
    pair.val = find_named_function (name);
    PushStack( Pair, run->e, &pair );
}

int main ()
{
    const unsigned N = 1;
    Runtime stacked_run;
    Runtime* run;
    run = &stacked_run;

    InitArray( TypeInfo, Simple_Types, N );
    InitArray( TypeInfoSet, Compound_Types, N );
    InitArray( InternalTypeInfo, Internal_Types, N );
    InitArray( NamedFunctionSet, Named_Functions, N );
    InitArray( Pair, run->d, N );
    InitArray( Pair, run->e, N );

    {
            /* Add the /any/ type, it's hardcoded. */
        pkey_t t;
        TypeInfoSet ts;
        ts.name = "any";
        ts.ntypes = 0;
        t = add_compound_type (&ts);
        assert (AnyType == t);
    }

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
        TypeInfo info;
        TypeInfoSet set;
        pkey_t types[10];
        const char* membs[10];

        info.types = types;

        info.name = "nil";
        info.nmembs = 0;
        add_simple_type (&info, 0);

        info.name = "yes";
        info.nmembs = 0;
        add_simple_type (&info, 0);

        info.name = "cons";
        info.nmembs = 2;
        types[0] = AnyType;
        membs[0] = "car";
        types[1] = AnyType | Compound_Types.n;
        membs[1] = "cdr";
        add_simple_type (&info, membs);

        set.name = "list";
        set.ntypes = 2;
        set.types = types;
        types[0] = find_simple_type ("cons");
        types[1] = find_simple_type ("nil");
        add_compound_type (&set);

        set.name = "bool";
        set.ntypes = 2;
        set.types = types;
        types[0] = find_simple_type ("yes");
        types[1] = find_simple_type ("nil");
        add_compound_type (&set);
    }

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

    {
        Function f;
        pkey_t types[10];
        Pair exprs[20];
        unsigned argmap[20];

        f.types = types;
        f.info.std.exprs = exprs;
        f.info.std.argmap = argmap;

        f.nargs = 2;
        f.type = StandardFunc;
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 0;
        types[0] = find_simple_type ("yes");
        types[1] = find_simple_type ("yes");
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("and", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("or", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("impl", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("eql", &f);

        types[0] = find_simple_type ("yes");
        types[1] = find_simple_type ("nil");
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("and", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("or", &f);
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("impl", &f);
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("eql", &f);

        types[0] = find_simple_type ("nil");
        types[1] = find_simple_type ("yes");
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("and", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("or", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("impl", &f);
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("eql", &f);

        types[0] = find_simple_type ("nil");
        types[1] = find_simple_type ("nil");
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("and", &f);
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("or", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("impl", &f);
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("eql", &f);

            /* (def (not (a nil)) (yes)) */
        f.nargs = 1;
        types[0] = find_simple_type ("nil");
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 0;
        exprs[0].key = find_simple_type ("yes");
        add_named_function ("not", &f);

            /* (def (not (a yes)) (nil)) */
        f.nargs = 1;
        types[0] = find_simple_type ("yes");
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 0;
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("not", &f);

            /* (def (cat (a nil) (b list)) b) */
        f.nargs = 2;
        types[0] = find_simple_type ("nil");
        types[1] = find_compound_type ("list");
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 1;
        exprs[0].key = 0;
        argmap[0] = 0;
        argmap[1] = 1;
        add_named_function ("cat", &f);

            /* (def (cat (a cons) (b list))
             *   (cons (car a)
             *         (cat (cdr a) b)))
             */
        f.nargs = 2;
        types[0] = find_simple_type ("cons");
        types[1] = find_compound_type ("list");
        f.info.std.nexprs = 7;
        f.info.std.nsubst = 3;
        exprs[0].key = CALLBIT | 2;
        exprs[0].val = find_named_function ("cons");
        exprs[1].key = CALLBIT | 1;
        exprs[1].val = find_named_function ("car");
        exprs[2].key = 0;
        argmap[0] = 2;
        argmap[1] = 0;
        exprs[3].key = CALLBIT | 2;
        exprs[3].val = find_named_function ("cat");
        exprs[4].key = CALLBIT | 1;
        exprs[4].val = find_named_function ("cdr");
        exprs[5].key = 0;
        argmap[2] = 5;
        argmap[3] = 0;
        exprs[6].key = 0;
        argmap[4] = 6;
        argmap[5] = 1;
        add_named_function ("cat", &f);

            /* (def (list a)
             *   (cons a nil))
             */
        f.nargs = 1;
        types[0] = find_compound_type ("any");
        f.info.std.nexprs = 3;
        f.info.std.nsubst = 1;
        exprs[0].key = CALLBIT | 2;
        exprs[0].val = find_named_function ("cons");
        exprs[1].key = 0;
        argmap[0] = 1;
        argmap[1] = 0;
        exprs[2].key = find_simple_type ("nil");
        add_named_function ("list", &f);
         
            /* (def (rev (a))) */
        f.nargs = 1;
        types[0] = find_simple_type ("nil");
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 0;
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("rev", &f);

            /* (def (rev (a cons))
             *   (cat (rev (cdr a))
             *        (list (car a))))
             */
        f.nargs = 1;
        types[0] = find_simple_type ("cons");
        f.info.std.nexprs = 7;
        f.info.std.nsubst = 2;
        exprs[0].key = CALLBIT | 2;
        exprs[0].val = find_named_function ("cat");
        exprs[1].key = CALLBIT | 1;
        exprs[1].val = find_named_function ("rev");
        exprs[2].key = CALLBIT | 1;
        exprs[2].val = find_named_function ("cdr");
        exprs[3].key = 0;
        argmap[0] = 3;
        argmap[1] = 0;
        exprs[4].key = CALLBIT | 1;
        exprs[4].val = find_named_function ("list");
        exprs[5].key = CALLBIT | 1;
        exprs[5].val = find_named_function ("car");
        exprs[6].key = 0;
        argmap[2] = 6;
        argmap[3] = 0;
        add_named_function ("rev", &f);

            /* (def (map (f func) (L nil))) */
        f.nargs = 2;
        types[0] = find_simple_type ("func");
        types[1] = find_simple_type ("nil");
        f.info.std.nexprs = 1;
        f.info.std.nsubst = 0;
        exprs[0].key = find_simple_type ("nil");
        add_named_function ("map", &f);

            /* (def (map (f func) (L cons))
             *   (cons (f (car L))
             *         (map f (cdr L)))
             */
        f.nargs = 2;
        types[0] = find_simple_type ("func");
        types[1] = find_simple_type ("cons");
        f.info.std.nexprs = 8;
        f.info.std.nsubst = 4;
        exprs[0].key = CALLBIT | 2;
        exprs[0].val = find_named_function ("cons");
        exprs[1].key = CALLBIT | 1;
        argmap[0] = 1;
        argmap[1] = 0;
        exprs[2].key = CALLBIT | 1;
        exprs[2].val = find_named_function ("car");
        exprs[3].key = 0;
        argmap[2] = 3;
        argmap[3] = 1;
        exprs[4].key = CALLBIT | 2;
        exprs[4].val = find_named_function ("map");
        exprs[5].key = 0;
        argmap[4] = 5;
        argmap[5] = 0;
        exprs[6].key = CALLBIT | 1;
        exprs[6].val = find_named_function ("cdr");
        exprs[7].key = 0;
        argmap[6] = 7;
        argmap[7] = 1;
        add_named_function ("map", &f);
    }

#if 0
#elif 0
    {push_function (run, "map", 2);
        {
            Pair pair;
            pair.key = find_simple_type ("func");
            pair.val = find_named_function ("list");
            PushStack( Pair, run->e, &pair );
        }
        push_function (run, "nil", 0);
    }

#elif 0
            push_function (run, "list", 1);
            push_function (run, "yes", 0);

#elif 1
    {push_function (run, "map", 2);
        {
            Pair pair;
            pair.key = find_simple_type ("func");
            pair.val = find_named_function ("not");
            PushStack( Pair, run->e, &pair );
        }
        {push_function (run, "cons", 2);
            push_function (run, "yes", 0);
            {push_function (run, "cons", 2);
                push_function (run, "nil", 0);
                {push_function (run, "cons", 2);
                    push_function (run, "yes", 0);
                    push_function (run, "nil", 0);
                }
            }
        }
    }

#elif 0
    {push_function (run, "car", 1);
        {push_function (run, "list", 1);
            {push_function (run, "list", 1);
                push_function (run, "yes", 0);
            }
        }
    }

#elif 0
    {push_function (run, "rev", 1);
        {push_function (run, "cons", 2);
            push_function (run, "yes", 0);
            {push_function (run, "cons", 2);
                push_function (run, "nil", 0);
                push_function (run, "nil", 0);
            }
        }
    }

#elif 0
    {push_function (run, "cat", 2);
        {push_function (run, "cons", 2);
            push_function (run, "yes", 0);
            push_function (run, "nil", 0);
        }
        {push_function (run, "cat", 2);
            {push_function (run, "cons", 2);
                push_function (run, "nil", 0);
                {push_function (run, "cons", 2);
                    push_function (run, "nil", 0);
                    push_function (run, "nil", 0);
                }
            }
            {push_function (run, "cons", 2);
                push_function (run, "yes", 0);
                {push_function (run, "cons", 2);
                    push_function (run, "yes", 0);
                    {push_function (run, "cons", 2);
                        push_function (run, "yes", 0);
                        push_function (run, "nil", 0);
                    }
                }
            }
        }
    }
#elif 0
    push_function (run, "cons", 2);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "nil", 0);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);

    push_function (run, "and", 2);
    push_function (run, "nil", 0);

    push_function (run, "or", 2);
    push_function (run, "nil", 0);
    push_function (run, "or", 2);
    push_function (run, "nil", 0);
    push_function (run, "or", 2);
    push_function (run, "nil", 0);
    push_function (run, "or", 2);
    push_function (run, "nil", 0);
    push_function (run, "or", 2);
    push_function (run, "nil", 0);
    push_function (run, "or", 2);
    push_function (run, "nil", 0);

        /* yes */
    push_function (run, "car", 1);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "cdr", 1);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "cons", 2);
    push_function (run, "yes", 0);
    push_function (run, "nil", 0);
#endif

    eval (run);

    CleanupArray( Pair, run->d );
    CleanupArray( Pair, run->e );
    CleanupArray( NamedFunctionSet, Named_Functions );
    CleanupArray( TypeInfo, Simple_Types );
    CleanupArray( TypeInfoSet, Compound_Types );
    free (Internal_Types.a);
    return 0;
}

