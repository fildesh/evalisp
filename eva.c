
#include "cx/bstree.h"
#include "cx/fileb.h"
#include "cx/rbtree.h"
#include "cx/sys-cx.h"

#include <assert.h>
#include <string.h>

typedef struct Cons Cons;


enum Cons_Kind {
    Cons_Cons, /* car is a Cons */
    Cons_cstr,
    Cons_NKinds
};
typedef enum Cons_Kind Cons_Kind;

struct Cons
{
    Cons* cdr;
    uint nrefs;
    Cons_Kind kind;
    union Cons_union {
        Cons* cons;
        char* cstr;
    } car;
};

DeclTableT( Cons, Cons );

    Cons*
make1_Cons (Cons* b)
{
    DeclAlloc( Cons, a, 1 );

    a->kind = Cons_NKinds;
    a->nrefs = 1;
    a->cdr = b;
    if (b)  ++ b->nrefs;

    return a;
}

Cons* make_Cons () { return make1_Cons (0); }

    void
free_Cons (Cons* a)
{
    while (a)
    {
        -- a->nrefs;
        if (a->nrefs > 0)  break;
        switch (a->kind)
        {
            case Cons_Cons:
                free_Cons (a->car.cons);
                break;
            case Cons_cstr:
                free (a->car.cstr);
                break;
            default:
                break;
        }

        {
            Cons* const b = a;
            a = a->cdr;
            free (b);
        }
    }
}


    void
dump_Cons (OFileB* of, Cons* a)
{
    dump_char_OFileB (of, '(');
    while (a)
    {
        switch (a->kind)
        {
            case Cons_Cons:
                dump_Cons (of, a->car.cons);
                break;
            case Cons_cstr:
                dump_cstr_OFileB (of, a->car.cstr);
                break;
            default:
                break;
        }
        a = a->cdr;
        if (a)
            dump_char_OFileB (of, ' ');
    }
    dump_char_OFileB (of, ')');
}


    Cons*
parse_lisp_XFileB (XFileB* xf)
{
    char delims[2+sizeof(WhiteSpaceChars)];
    char* s = 0;
    char c = 0;
    DeclTable( Cons, up );
    Cons* x = Grow1Table( up );
    x->cdr = 0;

    delims[0] = '(';
    delims[1] = ')';
    strcpy (&delims[2], WhiteSpaceChars);

    for (s = nextds_XFileB (xf, &c, delims);
         s;
         s = nextds_XFileB (xf, &c, delims))
    {
        Cons* y;
        if (s[0] != '\0')
        {
            x->cdr = make_Cons ();
            x = x->cdr;
            x->kind = Cons_cstr;
            x->car.cstr = dup_cstr (s);
        }

        if (c == '(')
        {
            x->cdr = make_Cons ();
            y = x->cdr;
            x = Grow1Table( up );
            x->cdr = 0;
            x->car.cons = y;
        }
        else if (c == ')')
        {
            if (up.sz == 1)
            {
                DBog0( "Too many closed parens!" );
                break;
            }

            y = &up.s[up.sz-1];
            x = y->car.cons;
            x->kind = Cons_Cons;
            x->car.cons = y->cdr;
            MPopTable( up, 1 );
        }
    }

    if (up.sz > 1)
    {
        { BLoop( i, up.sz-1 )
            Cons* y = &up.s[i+1];
            if (y->cdr)
            {
                free_Cons (y->cdr);
                y->cdr = 0;
            }
        } BLose()
        DBog1( "%u paren pairs need closing!", up.sz-1 );
    }

    x = up.s[0].cdr;
    LoseTable( up );
    return x;
}


    int
main ()
{
    XFileB* xf;
    OFileB* of;
    Cons* x;

    init_sys_cx ();

    xf = stdin_XFileB ();
    of = stderr_OFileB ();

    x = parse_lisp_XFileB (xf);
    dump_Cons (of, x);
    free_Cons (x);

    dump_char_OFileB (of, '\n');

    lose_sys_cx ();
    return 0;
}

