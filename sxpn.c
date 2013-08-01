/**
 * \file sxpn.c
 **/
#include "sxpn.h"

#include <stdarg.h>

    void
oput_ConsAtom (OFile* of, const ConsAtom* ca)
{
    switch (ca->kind)
    {
    case Cons_Cons:
        oput_Cons (of, ca->as.cons);
        break;
    case Cons_AlphaTab:
        oput_AlphaTab (of, &ca->as.alphatab);
        break;
    case Cons_cstr:
        oput_cstr_OFile (of, ca->as.cstr);
        break;
    case Cons_int:
        oput_int_OFile (of, ca->as.i);
        break;
    case Cons_uint:
        oput_uint_OFile (of, ca->as.ui);
        break;
    case Cons_ujint:
        oput_ujint_OFile (of, ca->as.uji);
        break;
    case Cons_real:
        oput_real_OFile (of, ca->as.re);
        break;
    default:
        break;
    }
}

    void
oput_Cons (OFile* of, const Cons* a)
{
    oput_char_OFile (of, '(');
    while (a)
    {
        oput_ConsAtom (of, &a->car);
        a = a->cdr;
        if (a)
            oput_char_OFile (of, ' ');
    }
    oput_char_OFile (of, ')');
}

    bool
addfn_Sxpn (Sxpn* sx, const char* name, const SxpnF* f)
{
    AlphaTab a = dflt_AlphaTab ();
    bool added = true;
    Assoc* e;

    copy_cstr_AlphaTab (&a, name);
    e = ensure1_Associa (&sx->fnmap, &a, &added);

    if (!added)
    {
        lose_AlphaTab (&a);
        return false;
    }

    key_fo_Assoc (e, &a);
    val_fo_Assoc (e, f);
    return true;
}

    bool
addkind_Sxpn (Sxpn* sx, const char* name, const ConsAtomKind* kind)
{
    AlphaTab a = dflt_AlphaTab ();
    bool added = false;
    Assoc* e;

    copy_cstr_AlphaTab (&a, name);
    e = ensure1_Associa (&sx->fnmap, &a, &added);

    if (!added)
    {
        lose_AlphaTab (&a);
        return false;
    }

    key_fo_Assoc (e, &a);
    val_fo_Assoc (e, kind);
    return true;
}

    Cons*
vtakef_Sxpn (Sxpn* sx, const char* fmt, va_list args)
{
    (void) sx;
    (void) fmt;
    (void) args;
    return 0;
}

#if 0
    Cons*
takef_Sxpn (Sxpn* sx, const char* fmt, ...)
{
    va_list args;
    va_start (args, fmt);
    vtakef_Sxpn (sx, fmt, args);
    va_end (args);
}

// "(%. %.. %&...)"
// First gets the ConsAtom associated with the element 1.
// Next gets the Cons associated with element 2.
// Last gets the pointer to the Cons of element 3.
// Nothing can be past a '...'.
// There must be >= 2 elements in this list.
// If there were no '...', there would have to be exactly 2 elements.
#endif

