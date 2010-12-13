

struct array_struct
{
    unsigned n;
    unsigned N;
    void*    a;
};
typedef struct array_struct Array;


#define InitArray( Type, arr, capacity ) \
    do { \
        (arr).n = 0; \
        (arr).N = capacity; \
        (arr).a = malloc ((arr).N * sizeof (Type)); \
    } while (0)

#if 0
static unsigned ARef_helper (const Array* arr, unsigned i)
{
    assert ((int) i >= 0);
    assert (i < arr->n);
    return i;
}
#define ARef( Type, arr, i ) \
    (&((Type*) (arr).a)[ARef_helper (&(arr), (unsigned) i)])
#else

#define dARef( Type, arr, i ) \
    (((Type*) (arr).a)[i])

#define ARef( Type, arr, i ) \
    (&dARef(Type, arr, i))

#endif

#define dARefLast( Type, arr ) \
    dARef( Type, arr, (arr).n - 1 )

#define ARefLast( Type, arr ) \
    ARef( Type, arr, (arr).n - 1 )


#define GrowArray( Type, arr, capac ) \
    do { \
        while ((arr).n + capac > (arr).N) \
        { \
            assert ((arr).N); \
            (arr).N *= 2; \
            (arr).a = realloc ((arr).a, (arr).N * sizeof (Type)); \
        } \
        (arr).n += capac; \
    } while (0)


#define dPushStack( Type, sk, elem ) \
    do { \
        GrowArray( Type, sk, 1 ); \
        dARefLast(Type, sk) = elem; \
    } while (0)

#define PushStack( Type, sk, elem ) \
    do { \
        GrowArray( Type, sk, 1 ); \
        memcpy (ARefLast(Type, sk), elem, sizeof (Type)); \
    } while (0)

#define dPopStack( Type, sk ) \
    dARef(Type, sk, -- (sk).n)

#define PopStack( Type, sk ) \
    (&dPopStack( Type, sk ))

#define CleanupArray( Type, arr ) \
    do { \
        unsigned i; \
        for (i = 0; i < (arr).n; ++i)  cleanup_##Type (ARef(Type, arr, i)); \
        free ((arr).a); \
        (arr).n = 0; \
        (arr).N = 0; \
        (arr).a = 0; \
    } while (0)

static void* MemDup_helper (const void* src, size_t size)
{
    void* dst = 0;
    if (size)
    {
        dst = malloc (size);
        memcpy (dst, src, size);
    }
    return dst;
}

#define MemDup( Type, src, len ) \
    ((Type*) MemDup_helper (src, (len) * sizeof (Type)))

