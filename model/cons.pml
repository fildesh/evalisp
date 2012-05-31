
  /* #define UseMemTable */
#define Max_n 3

#define Nil Max_n
#define TableSz byte
#define Max_TableSz 255

typedef Cons {
  TableSz nrefs;
  TableSz cdr;
};

TableSz nelems = 0;
Cons elems[Max_n];

  /* User references.*/
TableSz nrefs;
TableSz refs[Max_n];


TableSz nmems = 0;
#ifdef UseMemTable
  /* Things that can be added!*/
TableSz mems[Max_n];
#endif

inline initmem_Cons ()
{
  assert (nmems == 0);
  do
  :: nmems < Max_n ->
#ifdef UseMemTable
    mems[nmems] = nmems;
#endif
     elems[nmems].nrefs = Max_TableSz;
     nmems ++;
  :: else -> break;
  od;
}

inline make_Cons (x)
{
  assert (nmems > 0);
  nmems --;
#ifdef UseMemTable
  x = mems[nmems];
#else
  x = 0;
  do
  :: elems[x].nrefs == Max_TableSz ->
     break;
  :: else ->
     x ++;
     assert (x < Max_n);
  od;
#endif
}

inline free_Cons (x)
{
  elems[x].nrefs = Max_TableSz;
#ifdef UseMemTable
  mems[nmems] = x;
#endif
  nmems ++;
}

inline add_Cons (y)
{
  TableSz x = 0;

  make_Cons (x);

  elems[x].nrefs = 1;
  elems[x].cdr = y;

  if
  :: y != Nil ->
     elems[y].nrefs ++;
  :: else -> skip;
  fi;

  refs[nrefs] = x;
  nrefs ++;
  nelems ++;
}

inline del_Cons (i)
{
  TableSz x = refs[i];
  refs[i] = refs[nrefs-1];
  nrefs --;

  do
  :: x != Nil ->
     assert (elems[x].nrefs > 0);
     assert (elems[x].nrefs < Max_TableSz);
     elems[x].nrefs --;
     if
     :: elems[x].nrefs == 0 -> 
        free_Cons (x);
        x = elems[x].cdr;
        nelems --;
     :: else -> break;
     fi;
  :: else -> break;
  od;
}

init {
  TableSz i;

  initmem_Cons ();

  do
  :: atomic {
       nelems < Max_n ->
       select (i : 0..nrefs);
       if
       :: i == nrefs ->
          add_Cons (Nil);
       :: else ->
          add_Cons (refs[i]);
       fi;
     };
  :: atomic {
       nelems > 0 ->
       assert (nrefs > 0);
       select (i : 0..(nrefs-1));
       del_Cons (i);
     };
  :: else -> break;
  od;
}

