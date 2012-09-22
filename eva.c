
#include "cx/syscx.h"
#include "cx/fileb.h"
#include "cx/sxpn.h"

#include <string.h>

    Cons*
load_Sxpn (XFileB* xf, Sxpn* sx)
{
    char delims[2+sizeof(WhiteSpaceChars)];
    char* s = 0;
    char c = 0;
    Cons* up = take2_Sxpn (sx, dflt_Cons_ConsAtom (0), 0);
    Cons** p = &up->car.as.cons;

    delims[0] = '(';
    delims[1] = ')';
    strcpy (&delims[2], WhiteSpaceChars);

    for (s = nextds_XFileB (xf, &c, delims);
         s;
         s = nextds_XFileB (xf, &c, delims))
    {
        if (s[0] != '\0')
        {
            Cons* x = take_Sxpn (sx);
            *p = x;
            p = &x->cdr;
            x->car.kind = Cons_AlphaTab;
            x->car.as.alphatab = cons1_AlphaTab (s);
        }

        if (c == '(')
        {
            Cons* x = take2_Sxpn (sx, dflt_Cons_ConsAtom (0), 0);
            *p = x;
            p = &x->car.as.cons;

            up = take2_Sxpn (sx, dflt_Cons_ConsAtom (x), up);
        }
        else if (c == ')')
        {
            Cons* x;
            if (!up->cdr)
            {
                DBog0( "Too many closed parens!" );
                break;
            }

            x = up->car.as.cons;
            p = &x->cdr;

            up = pop_Sxpn (sx, up);
        }
    }

    if (up->cdr)
    {
        uint nopen = 0;
        while (up->cdr)
        {
            up = pop_Sxpn (sx, up);
            ++ nopen;
        }
        DBog1( "%u paren pairs need closing!", nopen );
    }

    {
        Cons* x = up->car.as.cons;
        up->car.as.cons = 0;
        give_Sxpn (sx, up);
        return x;
    }
}


    int
main (int argc, char** argv)
{
    int argi =
        (init_sysCx (&argc, &argv),
         1);
    DecloStack1( Sxpn, sx, dflt_Sxpn () );
    XFileB* xf = stdin_XFileB ();
    OFileB* of = stderr_OFileB ();
    Cons* x;

    if (argi < argc)
        failout_sysCx ("I don't take arguments from humans.");

    x = load_Sxpn (xf, sx);
    dump_Cons (of, x);
    give_Sxpn (sx, x);
    dump_char_OFileB (of, '\n');
    flush_OFileB (of);

    Claim2( sx->cells.sz ,==, 0 );
    lose_Sxpn (sx);
    lose_sysCx ();
    return 0;
}

