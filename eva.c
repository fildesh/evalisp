
#include "cx/bstree.h"
#include "cx/fileb.h"
#include "cx/sys-cx.h"

#include <assert.h>
#include <string.h>

    int
main ()
{
    char delims[2+sizeof(WhiteSpaceChars)];
    FileB* f;
    FileB* out;
    char* s = 0;
    char c = 0;
    uint depth = 0;

    init_sys_cx ();

    delims[0] = '(';
    delims[1] = ')';
    strcpy (&delims[2], WhiteSpaceChars);

    f = stdin_FileB ();
    out = stderr_FileB ();

    for (s = nextds_FileB (f, &c, delims);
         s;
         s = nextds_FileB (f, &c, delims))
    {
        if (c == '(')
        {
            dump_cstr_FileB (out, s);
            dump_char_FileB (out, '(');
            ++ depth;
        }
        else if (c == ')')
        {
            if (depth == 0)
            {
                DBog0( "Too many closed parens!" );
                break;
            }
            dump_cstr_FileB (out, s);
            dump_char_FileB (out, ')');
            -- depth;
        }
        else
        {
            dump_cstr_FileB (out, s);
            dump_char_FileB (out, ' ');
        }
    }
    dump_char_FileB (out, '\n');

    if (depth > 0)
        DBog1( "%u paren pairs need closing!", depth );

    lose_sys_cx ();
    return 0;
}

