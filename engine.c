#include "engine.h"
#include "regnodes.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

#define SIZEOF_ARRAY(a) (sizeof(a) / sizeof(a[0]))

#define TOLOWER(c) ((((c) >= 'A') && ((c) <= 'Z')) ? ((c) - 'A' + 'a') : (c))

#define LETTER_COUNT ('z' - 'a' + 1)

#define INFINITE_COUNT 32767

/* Regexp terms are normally regnodes, except for EXACT (and EXACTF)
   nodes, which can bundle many characters, which we have to compare
   separately. */
typedef struct
{
    regnode *rn;
    int spent;
} Arrow;

#define GET_LITERAL(a) (((char *)((a)->rn + 1)) + (a)->spent)
#define GET_BITMAP(a) ((unsigned char *)((a)->rn + 2))

#define GET_OFFSET(rn) ((rn)->next_off ? (rn)->next_off : get_synth_offset(rn))

/* Most functions below have this signature. The first parameter is a
   flag set after the comparison actually matched something, second
   parameter points into the first ("left") regexp passed into
   rc_compare, the third into the second ("right") regexp. Return
   value is 1 for match, 0 no match, -1 error (with the lowest-level
   failing function setting rc_error before returning it). */
typedef int (*FCompare)(int, Arrow *, Arrow *);

/* Place of a char in regexp bitmap. */
typedef struct
{
    int offs;
    unsigned char mask;
} BitFlag;

/* Set of chars and its complement formatted for convenient
   matching. */
typedef struct
{
  char *expl;
  int expl_size;
  char lookup[256];
  char nlookup[256];
  unsigned char bitmap[32];
  unsigned char nbitmap[32];
} ByteClass;

char *rc_error = 0;

/* matching \s i.e. not including \v - see perlre */
static char whitespace_expl[] = { ' ', '\f', '\n', '\r', '\t' };

static ByteClass whitespace;

static char digit_expl[10];

static ByteClass digit;

static char ndot_expl[] = { '\n' };

static ByteClass ndot;

static char alphanumeric_expl[11 + 2 * LETTER_COUNT];

static ByteClass alphanumeric;

/* true flags for ALNUM and its subsets, 0 otherwise */
static unsigned char alphanumeric_classes[OPTIMIZED];

/* true flags for NALNUM and its subsets, 0 otherwise */
static unsigned char non_alphanumeric_classes[OPTIMIZED];

static unsigned char trivial_nodes[OPTIMIZED];

static FCompare dispatch[OPTIMIZED][OPTIMIZED];

static int compare(int anchored, Arrow *a1, Arrow *a2);
static int compare_right_branch(int anchored, Arrow *a1, Arrow *a2);
static int compare_right_curly(int anchored, Arrow *a1, Arrow *a2);

static void init_bit_flag(BitFlag *bf, int c)
{
    assert(c >= 0);

    bf->offs = c / 8;
    bf->mask = 1 << (c % 8);
}

static void init_byte_class(ByteClass *bc, char *expl, int expl_size)
{
    BitFlag bf;
    int i;

    bc->expl = expl;
    bc->expl_size = expl_size;

    memset(bc->lookup, 0, sizeof(bc->lookup));
    memset(bc->nlookup, 1, sizeof(bc->nlookup));
    memset(bc->bitmap, 0, sizeof(bc->bitmap));
    memset(bc->nbitmap, 0xff, sizeof(bc->nbitmap));

    for (i = 0; i < expl_size; ++i)
    {
        bc->lookup[(unsigned char)expl[i]] = 1;
        bc->nlookup[(unsigned char)expl[i]] = 0;

	init_bit_flag(&bf, (unsigned char)expl[i]);
	bc->bitmap[bf.offs] |= bf.mask;
	bc->nbitmap[bf.offs] &= ~bf.mask;
    }
}

static void init_unfolded(char *unf, char c)
{
    *unf = TOLOWER(c);
    unf[1] = ((*unf >= 'a') && (*unf <= 'z')) ? *unf - 'a' + 'A' : *unf;
}

static int get_synth_offset(regnode *p)
{
    assert(!p->next_off);

    if (((p->type == EXACT) || (p->type == EXACTF)) && (p->flags == 1))
    {
	return 2;
    }
    else if (trivial_nodes[p->type] ||
	     (p->type == REG_ANY) || (p->type == SANY) ||
	     (p->type == ALNUM) || (p->type == NALNUM) ||
	     (p->type == SPACE) || (p->type == NSPACE) ||
	     (p->type == DIGIT) || (p->type == NDIGIT))
    {
	return 1;  
    }
    else if (p->type == ANYOF)
    {
	return 11;
    }
    else
    {
        /* fprintf(stderr, "type %d\n", p->type); */
	rc_error = "Offset not set";
	return -1;
    }

}

static int get_size(regnode *rn)
{
    int offs;
    regnode *e = rn;

    while (e->type != END)
    {
        offs = GET_OFFSET(e);
	if (offs <= 0)
	{
	    return -1;
	}

        e += offs;
    }

    return e - rn + 1;
}

static regnode *skip_sig(regnode *p)
{
    assert(p);

    if (!((p->flags == 156) &&
	(p->next_off == 0)))
    {
        /* fprintf(stderr, "%d %d %d\n", p->flags, p->type, p->next_off); */
        rc_error = "Invalid regexp signature";
	return 0;
    }

    return p + 1;
}

static regnode *alloc_alt(regnode *p, int sz)
{
    regnode *alt;

    alt = (regnode *)malloc(sizeof(regnode) * sz);
    if (!alt)
    {
	rc_error = "Could not allocate memory for regexp copy";
	return 0;
    }

    memcpy(alt, p, sizeof(regnode) * sz);

    return alt;
}

static int bump_exact(Arrow *a)
{
    int offs;

    assert((a->rn->type == EXACT) || (a->rn->type == EXACTF));

    offs = GET_OFFSET(a->rn); 
    if (offs <= 0)
    {
	return -1;
    }

    if (++(a->spent) >= a->rn->flags)
    {
	a->spent = 0;
	a->rn += offs;
    }

    return 1;
}

static int bump_regular(Arrow *a)
{
    int offs;

    assert(a->rn->type != END);
    assert(a->rn->type != EXACT);
    assert(a->rn->type != EXACTF);
    assert(!a->spent);

    offs = GET_OFFSET(a->rn); 
    if (offs <= 0)
    {
	return -1;
    }

    a->rn += offs;
    return 1;
}

static int bump_with_check(Arrow *a)
{
    if (a->rn->type == END)
    {
	return 0;
    }
    else if ((a->rn->type == EXACT) || (a->rn->type == EXACTF))
    {
        return bump_exact(a);
    }
    else
    {
        return bump_regular(a);
    }
}

static int get_jump_offset(regnode *p)
{
    int offs;
    regnode *q;

    assert(p->type != END);

    offs = GET_OFFSET(p);
    if (offs <= 0)
    {
	return -1;
    }

    q = p + offs;
    while (trivial_nodes[q->type])
    {
        offs = GET_OFFSET(q);
	if (offs <= 0)
	{
	    return -1;
	}

	q += offs;
    }

    return offs;
}

regexp *rc_regcomp(char *rs)
{
    PMOP *pm;
    char *end;
    regexp *rx;

    if (!rs)
    {
	croak("No regexp to compare");
    }

    Newz(1, pm, 1, PMOP);
    if (pm == 0)
    {
	rc_error = "Couldn't allocate memory for PMOP";
	return 0;
    }

    ENTER;
    SAVEDESTRUCTOR(safefree, pm);

    end = strchr(rs, '\0');
    rx = pregcomp(rs, end, pm);
    if (!rx)
    {
	croak("Cannot compile regexp");
    }

    LEAVE;

    return rx;
}

void rc_regfree(void *rx)
{
    if (rx)
    {
        pregfree(rx);
    }
}

static int compare_mismatch(int anchored, Arrow *a1, Arrow *a2)
{
    int rv;

    /* fprintf(stderr, "enter compare_mismatch(%d\n", anchored); */

    if (anchored)
    {
        return 0;
    }
    else
    {
        rv = bump_with_check(a1);
	if (rv <= 0)
	{
	    return rv;
	}

	return compare(0, a1, a2);
    }
}

static int compare_tails(int anchored, Arrow *a1, Arrow *a2)
{
    Arrow tail1, tail2;
    int rv;

    tail1.rn = a1->rn;
    tail1.spent = a1->spent;
    rv = bump_with_check(&tail1);
    if (rv <= 0)
    {
        return rv;
    }

    tail2.rn = a2->rn;
    tail2.spent = a2->spent;
    rv = bump_with_check(&tail2);
    if (rv <= 0)
    {
        return rv;
    }

    rv = compare(1, &tail1, &tail2);
    if (!rv)
    {
	rv = compare_mismatch(anchored, a1, a2);
    }

    return rv;
}

static int compare_left_tail(int anchored, Arrow *a1, Arrow *a2)
{
    Arrow tail1;
    int rv;

    tail1.rn = a1->rn;
    tail1.spent = a1->spent;
    rv = bump_with_check(&tail1);
    if (rv <= 0)
    {
        return rv;
    }

    return compare(anchored, &tail1, a2);
}

static int compare_bol(int anchored, Arrow *a1, Arrow *a2)
{
    int rv;

    assert((a1->rn->type == BOL) || (a1->rn->type == MBOL) ||
	(a1->rn->type == SBOL));

    if (anchored)
    {
        return 0;
    }

    if (bump_regular(a1) <= 0)
    {
        return -1;
    }

    rv = compare(1, a1, a2);
    if (!rv)
    {
	rv = compare_mismatch(0, a1, a2);
    }

    return rv;
}

static int compare_bitmaps(int anchored, Arrow *a1, Arrow *a2,
    unsigned char *b1, unsigned char *b2)
{
    int i;

    /* fprintf(stderr, "enter compare_bitmaps(%d, %d, %d\n", anchored,
       a1->rn->type, a2->rn->type); */

    for (i = 0; i < 32; ++i)
    {
	if (b1[i] & ~b2[i])
	{
	    /* fprintf(stderr, "compare_bitmaps fails at %d: %d does not imply %d\n",
	       i, b1[i], b2[i]); */
	    return compare_mismatch(anchored, a1, a2);
        }
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_anyof_multiline(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    Arrow tail1, tail2;
    unsigned char *bitmap;
    int i;
    unsigned char req;

    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == MBOL) || (a2->rn->type == MEOL));

    bitmap = GET_BITMAP(a1);
    init_bit_flag(&bf, '\n');

    for (i = 0; i < 32; ++i)
    {
        req = (i != bf.offs) ? 0 : bf.mask;
	if (bitmap[i] != req)
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    tail1.rn = a1->rn;
    tail1.spent = a1->spent;
    if (bump_regular(&tail1) <= 0)
    {
	return -1;
    }

    tail2.rn = a2->rn;
    tail2.spent = a2->spent;
    if (bump_regular(&tail2) <= 0)
    {
	return -1;
    }

    return compare(1, &tail1, &tail2);
}

static int compare_anyof_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    /* fprintf(stderr, "enter compare_anyof_anyof(%d\n", anchored); */

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        GET_BITMAP(a2));
}

/* compare_bitmaps could replace this method, but when a class
   contains just a few characters, it seems more natural to compare
   them explicitly */
static int compare_short_byte_class(int anchored, Arrow *a1, Arrow *a2,
    ByteClass *left)
{
    BitFlag bf;
    unsigned char *bitmap;
    int i;

    bitmap = GET_BITMAP(a2);
    for (i = 0; i < left->expl_size; ++i)
    {
        init_bit_flag(&bf, (unsigned char)left->expl[i]);
	if (!(bitmap[bf.offs] & bf.mask))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_alnum_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ALNUM);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, alphanumeric.bitmap,
        GET_BITMAP(a2));
}

static int compare_nalnum_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NALNUM);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, alphanumeric.nbitmap,
        GET_BITMAP(a2));
}

static int compare_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == SPACE);
    assert(a2->rn->type == ANYOF);

    return compare_short_byte_class(anchored, a1, a2,  &whitespace);
}

static int compare_reg_any_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == REG_ANY);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, ndot.nbitmap,
        GET_BITMAP(a2));
}

static int compare_nspace_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NSPACE);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, whitespace.nbitmap,
        GET_BITMAP(a2));
}

static int compare_digit_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    /* fprintf(stderr, "enter compare_digit_anyof\n"); */

    assert(a1->rn->type == DIGIT);
    assert(a2->rn->type == ANYOF);

    return compare_short_byte_class(anchored, a1, a2,  &digit);
}

static int compare_ndigit_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NDIGIT);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, digit.nbitmap,
        GET_BITMAP(a2));
}

static int compare_exact_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    unsigned char *bitmap;
    char *seq;

    /* fprintf(stderr, "enter compare_exact_anyof(%d, \n", anchored); */

    assert(a1->rn->type == EXACT);
    assert(a2->rn->type == ANYOF);

    seq = GET_LITERAL(a1);
    bitmap = GET_BITMAP(a2);
    init_bit_flag(&bf, (unsigned char)(*seq));
    if (!(bitmap[bf.offs] & bf.mask))
    {
        /* fprintf(stderr, "%c not in bitmap (bitmap[%d] = %d)\n",
	 *seq, bf.offs, bitmap[bf.offs]); */

        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    unsigned char *bitmap;
    char *seq;
    char unf[2];
    int i;

    /* fprintf(stderr, "enter compare_exactf_anyof(%d, \n", anchored); */

    assert(a1->rn->type == EXACTF);
    assert(a2->rn->type == ANYOF);

    seq = GET_LITERAL(a1);
    init_unfolded(unf, *seq);

    bitmap = GET_BITMAP(a2);

    for (i = 0; i < 2; ++i)
    {
        init_bit_flag(&bf, (unsigned char)unf[i]);
	if (!(bitmap[bf.offs] & bf.mask))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_byte_class(int anchored, Arrow *a1, Arrow *a2,
    char *lookup)
{
    char *seq;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));

    seq = GET_LITERAL(a1);

    if (!lookup[(unsigned char)(*seq)])
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_multiline(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == MBOL) || (a2->rn->type == MEOL));

    return compare_exact_byte_class(anchored, a1, a2,
        ndot.lookup);
}

static int compare_exact_alnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == ALNUM);

    return compare_exact_byte_class(anchored, a1, a2,
        alphanumeric.lookup);
}

static int compare_exact_nalnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NALNUM);

    return compare_exact_byte_class(anchored, a1, a2,
        alphanumeric.nlookup);
}

static int compare_exact_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == SPACE);

    return compare_exact_byte_class(anchored, a1, a2, whitespace.lookup);
}

static int compare_exact_nspace(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NSPACE);

    return compare_exact_byte_class(anchored, a1, a2, whitespace.nlookup);
}

static int compare_exact_digit(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == DIGIT);

    return compare_exact_byte_class(anchored, a1, a2, digit.lookup);
}

static int compare_exact_ndigit(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NDIGIT);

    return compare_exact_byte_class(anchored, a1, a2, digit.nlookup);
}

static int compare_anyof_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == REG_ANY);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        ndot.nbitmap);
}

static int compare_exact_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == REG_ANY);

    return compare_exact_byte_class(anchored, a1, a2, ndot.nlookup);
}

static int compare_anyof_alnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == ALNUM);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        alphanumeric.bitmap);
}

static int compare_anyof_nalnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NALNUM);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        alphanumeric.nbitmap);
}

static int compare_anyof_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == SPACE);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        whitespace.bitmap);
}

static int compare_anyof_nspace(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NSPACE);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        whitespace.nbitmap);
}

static int compare_anyof_digit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == DIGIT);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        digit.bitmap);
}

static int compare_anyof_ndigit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NDIGIT);

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1),
        digit.nbitmap);
}

static int compare_anyof_exact(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    unsigned char *bitmap, *seq;
    int i;
    unsigned char req;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == EXACT);

    bitmap = GET_BITMAP(a1);
    seq = GET_LITERAL(a2);
    init_bit_flag(&bf, (unsigned char)(*seq));

    for (i = 0; i < 32; ++i)
    {
        req = (i != bf.offs) ? 0 : bf.mask;
	if (bitmap[i] != req)
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_anyof_exactf(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    char unf[2];
    BitFlag bf[2];
    unsigned char right[32];
    int i;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == EXACTF);

    seq = GET_LITERAL(a2);
    init_unfolded(unf, *seq);

    for (i = 0; i < 2; ++i)
    {
	init_bit_flag(bf + i, unf[i]);
    }

    if (bf[0].offs == bf[1].offs)
    {
	bf[0].mask = bf[1].mask = bf[0].mask | bf[1].mask;
    }

    memset(right, 0, 32);
    for (i = 0; i < 2; ++i)
    {
        right[bf[i].offs] = bf[i].mask;
    }

    return compare_bitmaps(anchored, a1, a2, GET_BITMAP(a1), right);
}

static int compare_exact_exact(int anchored, Arrow *a1, Arrow *a2)
{
    char *q1, *q2;
    int rv;

    assert(a1->rn->type == EXACT);
    assert(a2->rn->type == EXACT);

    q1 = GET_LITERAL(a1);
    q2 = GET_LITERAL(a2);

    /* fprintf(stderr, "compare_exact_exact(%d, '%c', '%c')\n", anchored,
     *q1, *q2); */

    if (*q1 != *q2)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_exactf(int anchored, Arrow *a1, Arrow *a2)
{
    char *q1, *q2;
    char unf[2];

    assert(a1->rn->type == EXACT);
    assert(a2->rn->type == EXACTF);

    q1 = GET_LITERAL(a1);
    q2 = GET_LITERAL(a2);
    init_unfolded(unf, *q2);

    if ((*q1 != unf[0]) && (*q1 != unf[1]))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_exact(int anchored, Arrow *a1, Arrow *a2)
{
    char *q1, *q2;
    char unf[2];

    assert(a1->rn->type == EXACTF);
    assert(a2->rn->type == EXACT);

    q1 = GET_LITERAL(a1);
    init_unfolded(unf, *q1);
    q2 = GET_LITERAL(a2);

    if ((unf[0] != *q2) || (unf[1] != *q2))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_exactf(int anchored, Arrow *a1, Arrow *a2)
{
    char *q1, *q2;
    char l1, l2;

    assert(a1->rn->type == EXACTF);
    assert(a2->rn->type == EXACTF);

    q1 = GET_LITERAL(a1);
    q2 = GET_LITERAL(a2);

    l1 = TOLOWER(*q1);
    l2 = TOLOWER(*q2);

    if (l1 != l2)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_left_branch(int anchored, Arrow *a1, Arrow *a2)
{
    int rv, tsz;
    regnode *p1;
    Arrow left, right;

    /* fprintf(stderr, "enter compare_left_branch\n"); */

    assert(a1->rn->type == BRANCH);

    p1 = a1->rn;
    while (p1->type == BRANCH)
    {
        if (p1->next_off == 0)
	{
	    rc_error = "Branch with zero offset";
	    return -1;
	}

	left.rn = p1 + 1;
	left.spent = 0;

	right.rn = a2->rn;
	right.spent = a2->spent;

	rv = compare(anchored, &left, &right);
	/* fprintf(stderr, "rv = %d\n", rv); */

	if (rv < 0)
	{
	    return rv;
	}

	if (!rv)
	{
  	    /* fprintf(stderr, "compare_left_branch doesn't match\n"); */
	    return compare_mismatch(anchored, a1, a2);
	}

	p1 += p1->next_off;
    }

    a1->rn = p1;
    a1->spent = 0;

    tsz = get_size(a2->rn);
    if (tsz <= 0)
    {
	return -1;
    }

    a2->rn += tsz - 1;
    a2->spent = 0;

    return 1;
}

static int compare_anyof_branch(int anchored, Arrow *a1, Arrow *a2)
{
    unsigned char *bitmap;
    regnode *alt, *t1;
    Arrow left, right;
    int i, j, power, rv, sz, offs;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == BRANCH);

    bitmap = GET_BITMAP(a1);

    offs = GET_OFFSET(a1->rn);
    if (offs <= 0)
    {
	return -1;
    }

    t1 = a1->rn + offs;
    sz = get_size(t1);
    if (sz < 0)
    {
	return sz;
    }

    alt = (regnode *)malloc(sizeof(regnode) * (2 + sz));
    if (!alt)
    {
        rc_error = "Couldn't allocate memory for alternative copy";
	return -1;
    }

    alt[0].flags = 1;
    alt[0].type = EXACT;
    alt[0].next_off = 2;
    memcpy(alt + 2, t1, sizeof(regnode) * sz);

    right.rn = 0;

    for (i = 0; i < 32; ++i)
    {
        power = 1;
	for (j = 0; j < 8; ++j)
	{
	    if (bitmap[i] & power)
	    {
	        alt[1].flags = 8 * i + j;
		left.rn = alt;
		left.spent = 0;

		right.rn = a2->rn;
		right.spent = a2->spent;

		rv = compare_right_branch(anchored, &left, &right);
		if (rv < 0)
		{
		    free(alt);
		    return rv;
		}

		if (!rv)
		{
		    free(alt);
		    return compare_mismatch(anchored, a1, a2);
		}
	    }

	    power *= 2;
	}
    }

    free(alt);

    if (!right.rn)
    {
	rc_error = "Empty mask not supported";
	return -1;
    }

    a1->rn = t1 + sz - 1;
    assert(a1->rn->type == END);
    a1->spent = 0;

    a2->rn = right.rn;
    a2->spent = right.spent;

    return 1;
}

static int compare_right_branch(int anchored, Arrow *a1, Arrow *a2)
{
    int rv;
    regnode *p2;
    Arrow left, right;

    /* fprintf(stderr, "enter compare_right_branch\n"); */

    assert(a2->rn->type == BRANCH);

    p2 = a2->rn;
    rv = 0;
    while ((p2->type == BRANCH) && !rv)
    {
      /* fprintf(stderr, "p2->type = %d\n", p2->type); */

	left.rn = a1->rn;
	left.spent = a1->spent;

        if (p2->next_off == 0)
	{
	    rc_error = "Branch with offset zero";
	    return -1;
	}

	right.rn = p2 + 1;
	right.spent = 0;

	rv = compare(anchored, &left, &right);
	/* fprintf(stderr, "got %d\n", rv); */

	p2 += p2->next_off;
    }

    if (rv < 0)
    {
	return rv;
    }

    if (!rv)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    a1->rn = left.rn;
    a1->spent = left.spent;

    a2->rn = right.rn;
    a2->spent = right.spent;

    return 1;
}

static int compare_right_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2;
    Arrow left, right;
    int sz, rv, offs;

    /* fprintf(stderr, "enter compare_right_star\n"); */

    p2 = a2->rn;
    assert(p2->type == STAR);

    sz = get_size(p2);
    if (sz < 0)
    {
	return sz;
    }

    left.rn = a1->rn;
    left.spent = a1->spent;

    offs = GET_OFFSET(p2);
    if (offs <= 0)
    {
	return -1;
    }

    right.rn = p2 + offs;
    right.spent = 0;

    rv = compare(anchored, &left, &right);
    if (rv < 0)
    {
	return rv;
    }

    if (rv == 0)
    {
	right.rn = p2 + 1;
	right.spent = 0;

	rv = compare(anchored, a1, &right);
	if (rv < 0)
	{
	    return rv;
	}

	if (!rv)
	{
	    return compare_mismatch(anchored, a1, a2);
	}

	right.rn = p2;
	right.spent = 0;

	rv = compare_right_star(1, a1, &right);
    }

    if (rv <= 0)
    {
        return rv;
    }

    a2->rn += sz - 1;
    assert(a2->rn->type == END);
    a2->spent = 0;

    return rv;
}

static int compare_repeat_repeat(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;

    p1 = a1->rn;
    assert((p1->type == PLUS) || (p1->type == STAR));
    p2 = a2->rn;
    assert((p2->type == PLUS) || (p2->type == STAR));

    left.rn = p1 + 1;
    left.spent = 0;

    right.rn = p2 + 1;
    right.spent = 0;

    return compare(1, &left, &right);
}

static int compare_right_curly_from_zero(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2, *alt;
    short n, *cnt;
    Arrow left, right;
    int sz, rv, offs;

    p2 = a2->rn;

    n = ((short *)(p2 + 1))[1];
    if (n <= 0)
    {
	rc_error = "Curly must have positive maximum";
	return -1;
    }

    sz = get_size(p2);
    if (sz < 0)
    {
	return sz;
    }

    left.rn = a1->rn;
    left.spent = a1->spent;

    offs = GET_OFFSET(p2);
    if (offs <= 0)
    {
	return -1;
    }

    right.rn = p2 + offs;
    right.spent = 0;

    rv = compare(anchored, &left, &right);
    if (rv < 0)
    {
	return rv;
    }

    if (rv == 0)
    {
        alt = alloc_alt(p2, sz);
	if (!alt)
	{
	    return -1;
	}

	right.rn = alt + 2;
	right.spent = 0;

	rv = compare(anchored, a1, &right);
	if (rv < 0)
	{
	    free(alt);
	    return rv;
	}

	if (!rv)
	{
	    free(alt);
	    return compare_mismatch(anchored, a1, a2);
	}

	cnt = (short *)(alt + 1);
	if (cnt[1] < INFINITE_COUNT)
	{
	    --cnt[1];
	}

	if (cnt[1] > 0)
	{
	    right.rn = alt;
	    right.spent = 0;

	    rv = compare_right_curly_from_zero(1, a1, &right);
	}
	else
	{
  	    rv = 1;
	}

	free(alt);
    }

    if (rv <= 0)
    {
        return rv;
    }

    a2->rn += sz - 1;
    assert(a2->rn->type == END);
    a2->spent = 0;

    return rv;
}

static int compare_left_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *alt, *q;
    Arrow left, right;
    int sz, rv, offs, end_offs;
    unsigned char orig_type;

    p1 = a1->rn;
    assert(p1->type == PLUS);

    sz = get_size(p1);
    if (sz < 0)
    {
	return -1;
    }

    if (sz < 2)
    {
	rc_error = "Left plus offset too small";
	return -1;
    }

    alt = alloc_alt(p1 + 1, sz - 1);
    if (!alt)
    {
	return -1;
    }

    if (anchored)
    {
	offs = get_jump_offset(p1);
	if (offs <= 0)
	{
	    return -1;
	}

	q = p1 + offs;
	if (q->type != END)
	{
	    /* repeat with a tail after it can be more strict than a
	       fixed-length match only if the tail is at least as
	       strict as the repeated regexp */
	    left.rn = q;
	    left.spent = 0;

	    end_offs = offs - 1;
	    orig_type = alt[end_offs].type;
	    alt[end_offs].type = END;

	    right.rn = alt;
	    right.spent = 0;

	    /* fprintf(stderr, "comparing %d to %d\n", left.rn->type,
	       right.rn->type); */
	    rv = compare(1, &left, &right);
	    /* fprintf(stderr, "compare returned %d\n", rv); */
	    if (rv <= 0)
	    {
		free(alt);
		return rv;
	    }

	    alt[end_offs].type = orig_type;
	}
    }

    left.rn = alt;
    left.spent = 0;
    rv = compare(anchored, &left, a2);
    free(alt);
    return rv;
}

static int compare_right_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2;
    Arrow right;
    int sz, rv;

    p2 = a2->rn;
    assert(p2->type == PLUS);

    /* fprintf(stderr, "enter compare_right_plus\n"); */

    sz = get_size(p2);
    if (sz < 0)
    {
	return -1;
    }

    if (sz < 2)
    {
	rc_error = "Plus offset too small";
	return -1;
    }

    /* fprintf(stderr, "sz = %d\n", sz); */

    right.rn = p2 + 1;
    right.spent = 0;

    rv = compare(anchored, a1, &right);

    if (rv < 0)
    {
	return rv;
    }

    if (!rv)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    a2->rn += sz - 1;
    assert(a2->rn->type == END);
    a2->spent = 0;

    return rv;
}

static int compare_next(int anchored, Arrow *a1, Arrow *a2)
{
    if (bump_regular(a2) <= 0)
    {
        return -1;
    }

    return compare(anchored, a1, a2);
}

static int compare_curly_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;
    short *cnt;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));
    p2 = a2->rn;
    assert(p2->type == PLUS);

    cnt = (short *)(p2 + 1);
    if (cnt[0] < 0)
    {
	rc_error = "Negative minimum for curly";
	return -1;
    }

    if (!cnt[0])
    {
        return compare_mismatch(anchored, a1, a2);
    }

    left.rn = p1 + 2;
    left.spent = 0;

    right.rn = p2 + 1;
    right.spent = 0;

    return compare(1, &left, &right);
}

static int compare_curly_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;
    short *cnt;
    int rv;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));
    p2 = a2->rn;
    assert(p2->type == STAR);

    left.rn = p1 + 2;
    left.spent = 0;

    right.rn = p2 + 1;
    right.spent = 0;

    rv = compare(1, &left, &right);
    if (!rv)
    {
	rv = compare_next(anchored, a1, a2);
    }

    return rv;
}

static int compare_plus_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *e2;
    Arrow left, right;
    short *cnt;
    int rv, offs;

    p1 = a1->rn;
    assert(p1->type == PLUS);
    p2 = a2->rn;
    assert((p2->type == CURLY) || (p2->type == CURLYM) ||
	   (p2->type == CURLYX));

    cnt = (short *)(p2 + 1);
    if (cnt[0] < 0)
    {
	rc_error = "Negative minimum for curly";
	return -1;
    }

    if (cnt[0] > 1) /* FIXME: fails '(?:aa)+' => 'a{2,}' */
    {
        return compare_mismatch(anchored, a1, a2);
    }

    left.rn = p1 + 1;
    left.spent = 0;

    if (cnt[1] != INFINITE_COUNT)
    {
        offs = get_jump_offset(p2);
	if (offs <= 0)
	{
	    return -1;
	}

	e2 = p2 + offs;
	if (e2->type != END)
	{
	    return compare_mismatch(anchored, a1, a2);	    
	}
    }

    right.rn = p2 + 2;
    right.spent = 0;

    rv = compare(1, &left, &right);
    return (!rv && !cnt[0]) ? compare_next(anchored, a1, a2) : rv;
}

static void dec_curly_counts(short *altcnt)
{
    --altcnt[0];
    if (altcnt[1] < INFINITE_COUNT)
    {
	--altcnt[1];
    }
}

static int compare_left_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *alt, *q;
    Arrow left, right;
    int sz, rv, offs, end_offs;
    unsigned char orig_type;
    short *cnt;

    /* fprintf(stderr, "enter compare_left_curly(%d, %d, %d)\n", anchored,
       a1->rn->type, a2->rn->type); */

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));

    cnt = (short *)(p1 + 1);
    if (!cnt[0])
    {
        /* fprintf(stderr, "curly from 0\n"); */
	return compare_mismatch(anchored, a1, a2);
    }

    sz = get_size(p1);
    if (sz < 0)
    {
	return -1;
    }

    if (sz < 3)
    {
	rc_error = "Left curly offset too small";
	return -1;
    }

    if (cnt[0] > 1)
    {
        /* fprintf(stderr, "curly with non-trivial repeat count\n"); */

	offs = GET_OFFSET(p1);
	if (offs < 0)
	{
	    return -1;
	}
	
	if (offs < 3)
	{
	    rc_error = "Left curly offset is too small";
	    return -1;
	}

        alt = (regnode *)malloc(sizeof(regnode) * (offs - 2 + sz));
	if (!alt)
	{
	    rc_error = "Could not allocate memory for unrolled curly";
	    return -1;
	}

	memcpy(alt, p1 + 2, (offs - 2) * sizeof(regnode));
	memcpy(alt + offs - 2, p1, sz * sizeof(regnode));

	dec_curly_counts((short *)(alt + offs - 1));

	left.rn = alt;
	left.spent = 0;
	rv = compare(1, &left, a2);
	free(alt);
	return rv;
    }

    if (anchored && !((cnt[0] == 1) && (cnt[1] == 1)))
    {
        /* fprintf(stderr, "anchored curly with variable length\n"); */

	alt = alloc_alt(p1 + 2, sz - 2);
	if (!alt)
	{
	    return -1;
	}

	offs = get_jump_offset(p1);
	if (offs <= 0)
	{
	    return -1;
	}

	q = p1 + offs;
	if (q->type != END)
	{
	    /* repeat with a tail after it can be more strict than a
	       fixed-length match only if the tail is at least as
	       strict as the repeated regexp */
	    left.rn = q;
	    left.spent = 0;

	    end_offs = offs - 1;
	    alt[end_offs].type = END;

	    right.rn = alt;
	    right.spent = 0;

	    /* fprintf(stderr, "comparing %d to %d\n", left.rn->type,
	       right.rn->type); */
	    rv = compare(1, &left, &right);
	    free(alt);
	    /* fprintf(stderr, "compare returned %d\n", rv); */
	    if (rv <= 0)
	    {
		return rv;
	    }
	}
    }

    left.rn = p1 + 2;
    left.spent = 0;
    return compare(anchored, &left, a2);
}

static int compare_right_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2, *alt;
    Arrow right;
    short *cnt, *altcnt;
    int sz, rv, offs, nanch;

    p2 = a2->rn;

    cnt = (short *)(p2 + 1);
    if (cnt[0] < 0)
    {
	rc_error = "Curly has negative minimum";
	return -1;
    }

    /* fprintf(stderr, "compare_right_curly from %d\n", cnt[0]); */

    nanch = anchored;

    if (cnt[0] > 0)
    {
        /* the repeated expression is mandatory: */
        sz = get_size(p2);
	if (sz < 0)
	{
	    return sz;
	}

	if (sz < 3)
	{
	    rc_error = "Right curly offset too small";
	    return -1;
	}

	/* we can match it once and recurse (works for
	   e.g. '.$' vs. '.{3}$')... */
	right.rn = p2 + 2;
	right.spent = 0;

	rv = compare(anchored, a1, &right);
	if (rv < 0)
	{
	    return rv;
	}

	if (!rv)
	{
	    /* ...or (if we aren't anchored yet) just do the left tail... */
	    rv = compare_mismatch(anchored, a1, a2);
	    if (rv)
	    {
		return rv;
	    }

	    /* ...or (last try) unroll the repeat (works for e.g.
	       'abbc' vs. 'ab{2}c' */
	    if (cnt[0] > 1)
	    {
		offs = GET_OFFSET(p2);
		if (offs < 0)
		{
		    return -1;
		}

		if (offs < 3)
		{
		    rc_error = "Left curly offset is too small";
		    return -1;
		}

		alt = (regnode *)malloc(sizeof(regnode) * (offs - 2 + sz));
		if (!alt)
		{
		    rc_error = "Couldn't allocate memory for unrolled curly";
		    return -1;
		}

		memcpy(alt, p2 + 2, (offs - 2) * sizeof(regnode));
		memcpy(alt + offs - 2, p2, sz * sizeof(regnode));

		dec_curly_counts((short *)(alt + offs - 1));

		right.rn = alt;
		right.spent = 0;

		rv = compare(anchored, a1, &right);
		free(alt);
		return rv;
	    }

	    return 0;
	}

	/* strictly speaking, matching one repeat didn't *necessarily*
	   anchor the match, but we'll ignore such cases as
	   pathological */
	nanch = 1;

	alt = alloc_alt(p2, sz);
	if (!alt)
	{
	    return -1;
	}

	altcnt = (short *)(alt + 1);
	dec_curly_counts(altcnt);
	if (altcnt[1] > 0)
	{
	    right.rn = alt;
	    right.spent = 0;

	    rv = compare_right_curly(nanch, a1, &right);
	}
	else
	{
  	    rv = 1;
	}

	free(alt);

	if (rv <= 0)
	{
	    return rv;
	}

	a2->rn += sz - 1;
	assert(a2->rn->type == END);
	a2->spent = 0;

	return rv;
    }

    return compare_right_curly_from_zero(nanch, a1, a2);
}

static int compare_curly_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *e2;
    Arrow left, right;
    short *cnt1, *cnt2;
    int sz1, rv, offs;

    /* fprintf(stderr, "enter compare_curly_curly\n"); */

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));
    p2 = a2->rn;
    assert((p2->type == CURLY) || (p2->type == CURLYM) ||
	   (p2->type == CURLYX));

    cnt1 = (short *)(p1 + 1);
    if (cnt1[0] < 0)
    {
	rc_error = "Negative minimum for left curly";
	return -1;
    }

    cnt2 = (short *)(p2 + 1);
    if (cnt2[0] < 0)
    {
	rc_error = "Negative minimum for right curly";
	return -1;
    }

    if (cnt2[0] > cnt1[0]) /* FIXME: fails '(?:aa){1,}' => 'a{2,}' */
    {
        return compare_mismatch(anchored, a1, a2);
    }

    left.rn = p1 + 2;
    left.spent = 0;

    if (cnt1[1] > cnt2[1])
    {
	offs = get_jump_offset(p2);
	if (offs <= 0)
	{
	    return -1;
	}

	e2 = p2 + offs;
	if (e2->type != END)
	{
	    return compare_mismatch(anchored, a1, a2);	    
	}
    }

    right.rn = p2 + 2;
    right.spent = 0;

    /* fprintf(stderr, "comparing tails\n"); */
    rv = compare(1, &left, &right);
    /* fprintf(stderr, "tail compare returned %d\n", rv); */
    return (!rv && !cnt2[0]) ? compare_next(anchored, a1, a2) : rv;
}

static int compare_bound(int anchored, Arrow *a1, Arrow *a2,
    int move_left, unsigned char *bitmap, char *lookup,
    unsigned char *oktypes)
{
    Arrow left, right;
    unsigned char *b1;
    unsigned char t;
    int i;
    char *seq;

    assert((a2->rn->type == BOUND) || (a2->rn->type == NBOUND));

    left.rn = a1->rn;
    left.spent = a1->spent;

    if (bump_with_check(&left) <= 0)
    {
	return -1;
    }

    t = left.rn->type;
    if (t >= OPTIMIZED)
    {
        rc_error = "Invalid node type";
        return -1;
    }
    else if (t == ANYOF)
    {
        /* fprintf(stderr, "next is bitmap\n"); */

        b1 = GET_BITMAP(&left);
	for (i = 0; i < 32; ++i)
	{
	    if (b1[i] & ~bitmap[i])
	    {
		return compare_mismatch(anchored, a1, a2);
	    }
	}
    }
    else if ((t == EXACT) || (t == EXACTF))
    {
        seq = GET_LITERAL(&left);
	if (!lookup[(unsigned char)(*seq)])
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }
    else if (!oktypes[t])
    {
	return compare_mismatch(anchored, a1, a2);
    }

    right.rn = a2->rn;
    right.spent = a2->spent;
    if (bump_with_check(&right) <= 0)
    {
	return -1;
    }

    return move_left ? compare(1, &left, &right) : 
        compare(anchored, a1, &right);
}

static int compare_bol_word(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 1, alphanumeric.bitmap,
        alphanumeric.lookup, alphanumeric_classes);
}

static int compare_bol_nword(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 1, alphanumeric.nbitmap,
        alphanumeric.nlookup, non_alphanumeric_classes);
}

static int compare_next_word(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 0, alphanumeric.bitmap,
        alphanumeric.lookup, alphanumeric_classes);
}

static int compare_next_nword(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 0, alphanumeric.nbitmap,
        alphanumeric.nlookup, non_alphanumeric_classes);
}

static int compare_anyof_bounds(int anchored, Arrow *a1, Arrow *a2,
    unsigned char *bitmap)
{
    unsigned char *b1;
    FCompare cmp[3];
    int i;

    cmp[0] = compare_next_word;
    cmp[1] = compare_next_nword;
    cmp[2] = compare_mismatch;

    b1 = GET_BITMAP(a1);
    for (i = 0; (i < 32) && (cmp[0] || cmp[1]); ++i)
    {
        if (b1[i] & ~bitmap[i])
	{
	     cmp[0] = 0;
	}

        if (b1[i] & bitmap[i])
	{
	     cmp[1] = 0;
	}
    }

    for (i = 0; i < SIZEOF_ARRAY(cmp); ++i)
    {
        if (cmp[i])
	{
	    return (cmp[i])(anchored, a1, a2);
	}
    }
}

static int compare_anyof_bound(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == BOUND);

    return compare_anyof_bounds(anchored, a1, a2, alphanumeric.nbitmap);
}

static int compare_anyof_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NBOUND);

    return compare_anyof_bounds(anchored, a1, a2, alphanumeric.bitmap);
}

static int compare_exact_bound(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    FCompare cmp;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == BOUND);

    seq = GET_LITERAL(a1);

    cmp = alphanumeric.lookup[(unsigned char)(*seq)] ?
        compare_next_nword : compare_next_word;
    return cmp(anchored, a1, a2);
}

static int compare_exact_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    FCompare cmp;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NBOUND);

    seq = GET_LITERAL(a1);

    cmp = alphanumeric.lookup[(unsigned char)(*seq)] ?
        compare_next_word : compare_next_nword;
    return cmp(anchored, a1, a2);
}

static int success(int anchored, Arrow *a1, Arrow *a2)
{
    return 1;
}

int rc_compare(regnode *p1, regnode *p2)
{
    Arrow a1, a2;

    p1 = skip_sig(p1);
    if (!p1)
    {
	return -1;
    }

    p2 = skip_sig(p2);
    if (!p2)
    {
	return -1;
    }

    a1.rn = p1;
    a1.spent = 0;
    a2.rn = p2;
    a2.spent = 0;

    return compare(0, &a1, &a2);
}

static int compare(int anchored, Arrow *a1, Arrow *a2)
{
    FCompare cmp;

    /* fprintf(stderr, "enter compare(%d, %d, %d)\n", anchored,
       a1->rn->type, a2->rn->type); */

    if ((a1->rn->type >= OPTIMIZED) || (a2->rn->type >= OPTIMIZED))
    {
        rc_error = "Invalid regexp node type";
        return -1;
    }

    cmp = dispatch[a1->rn->type][a2->rn->type];
    if (!cmp)
    {
        /* fprintf(stderr, "no comparator\n"); */
	return 0;
    }

    return cmp(anchored, a1, a2);
}

void rc_init()
{
    int i, wstart;

    init_byte_class(&whitespace, whitespace_expl,
        SIZEOF_ARRAY(whitespace_expl));

    for (i = 0; i < SIZEOF_ARRAY(digit_expl); ++i)
    {
	digit_expl[i] = '0' + i;
    }

    init_byte_class(&digit, digit_expl, SIZEOF_ARRAY(digit_expl));

    init_byte_class(&ndot, ndot_expl, SIZEOF_ARRAY(ndot_expl));

    alphanumeric_expl[0] = '_';

    wstart = 1;
    memcpy(alphanumeric_expl + wstart, digit_expl, 10 * sizeof(char));

    wstart += 10;
    for (i = 0; i < LETTER_COUNT; ++i)
    {
	alphanumeric_expl[wstart + i] = 'a' + i;
    }

    wstart += LETTER_COUNT;
    for (i = 0; i < LETTER_COUNT; ++i)
    {
	alphanumeric_expl[wstart + i] = 'A' + i;
    }

    init_byte_class(&alphanumeric, alphanumeric_expl,
        SIZEOF_ARRAY(alphanumeric_expl));

    memset(alphanumeric_classes, 0, SIZEOF_ARRAY(alphanumeric_classes));
    alphanumeric_classes[ALNUM] = alphanumeric_classes[DIGIT] = 1;

    memset(non_alphanumeric_classes, 0,
	SIZEOF_ARRAY(non_alphanumeric_classes));
    non_alphanumeric_classes[NALNUM] = non_alphanumeric_classes[SPACE] = 
        non_alphanumeric_classes[EOL] = non_alphanumeric_classes[SEOL] = 1;

    memset(trivial_nodes, 0, SIZEOF_ARRAY(trivial_nodes));
    trivial_nodes[SUCCEED] = trivial_nodes[NOTHING] =
        trivial_nodes[WHILEM] = 1;

    memset(dispatch, 0, sizeof(FCompare) * OPTIMIZED * OPTIMIZED);

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][END] = success;
    }

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][SUCCEED] = compare_next;
    }

    dispatch[SUCCEED][SUCCEED] = compare_tails;

    dispatch[SUCCEED][BOL] = compare_left_tail;
    dispatch[BOL][BOL] = compare_tails;
    dispatch[SBOL][BOL] = compare_tails;
    dispatch[BRANCH][BOL] = compare_left_branch;
    dispatch[NOTHING][BOL] = compare_left_tail;
    dispatch[STAR][BOL] = compare_mismatch;
    dispatch[PLUS][BOL] = compare_left_plus;
    dispatch[CURLY][BOL] = compare_left_curly;
    dispatch[CURLYM][BOL] = compare_left_curly;
    dispatch[CURLYX][BOL] = compare_left_curly;
    dispatch[WHILEM][BOL] = compare_left_tail;
    dispatch[MINMOD][BOL] = compare_left_tail;

    dispatch[SUCCEED][MBOL] = compare_left_tail;
    dispatch[BOL][MBOL] = compare_tails;
    dispatch[MBOL][MBOL] = compare_tails;
    dispatch[SBOL][MBOL] = compare_tails;
    dispatch[REG_ANY][MBOL] = compare_mismatch;
    dispatch[SANY][MBOL] = compare_mismatch;
    dispatch[ANYOF][MBOL] = compare_anyof_multiline;
    dispatch[ALNUM][MBOL] = compare_mismatch;
    dispatch[NALNUM][MBOL] = compare_mismatch;
    dispatch[SPACE][MBOL] = compare_mismatch;
    dispatch[NSPACE][MBOL] = compare_mismatch;
    dispatch[DIGIT][MBOL] = compare_mismatch;
    dispatch[NDIGIT][MBOL] = compare_mismatch;
    dispatch[BRANCH][MBOL] = compare_left_branch;
    dispatch[EXACT][MBOL] = compare_exact_multiline;
    dispatch[EXACTF][MBOL] = compare_exact_multiline;
    dispatch[NOTHING][MBOL] = compare_left_tail;
    dispatch[STAR][MBOL] = compare_mismatch;
    dispatch[PLUS][MBOL] = compare_left_plus;
    dispatch[CURLY][MBOL] = compare_left_curly;
    dispatch[CURLYM][MBOL] = compare_left_curly;
    dispatch[CURLYX][MBOL] = compare_left_curly;
    dispatch[WHILEM][MBOL] = compare_left_tail;
    dispatch[MINMOD][MBOL] = compare_left_tail;

    dispatch[SUCCEED][SBOL] = compare_left_tail;
    dispatch[BOL][SBOL] = compare_tails;
    dispatch[SBOL][SBOL] = compare_tails;
    dispatch[BRANCH][SBOL] = compare_left_branch;
    dispatch[NOTHING][SBOL] = compare_left_tail;
    dispatch[STAR][SBOL] = compare_mismatch;
    dispatch[PLUS][SBOL] = compare_left_plus;
    dispatch[CURLY][SBOL] = compare_left_curly;
    dispatch[CURLYM][SBOL] = compare_left_curly;
    dispatch[CURLYX][SBOL] = compare_left_curly;
    dispatch[WHILEM][SBOL] = compare_left_tail;
    dispatch[MINMOD][SBOL] = compare_left_tail;

    dispatch[SUCCEED][EOL] = compare_left_tail;
    dispatch[EOL][EOL] = compare_tails;
    dispatch[SEOL][EOL] = compare_tails;
    dispatch[BRANCH][EOL] = compare_left_branch;
    dispatch[NOTHING][EOL] = compare_left_tail;
    dispatch[STAR][EOL] = compare_mismatch;
    dispatch[PLUS][EOL] = compare_left_plus;
    dispatch[CURLY][EOL] = compare_left_curly;
    dispatch[CURLYM][EOL] = compare_left_curly;
    dispatch[CURLYX][EOL] = compare_left_curly;
    dispatch[WHILEM][EOL] = compare_left_tail;
    dispatch[MINMOD][EOL] = compare_left_tail;

    dispatch[SUCCEED][MEOL] = compare_left_tail;
    dispatch[EOL][MEOL] = compare_tails;
    dispatch[MEOL][MEOL] = compare_tails;
    dispatch[SEOL][MEOL] = compare_tails;
    dispatch[REG_ANY][MEOL] = compare_mismatch;
    dispatch[SANY][MEOL] = compare_mismatch;
    dispatch[ANYOF][MEOL] = compare_anyof_multiline;
    dispatch[ALNUM][MEOL] = compare_mismatch;
    dispatch[NALNUM][MEOL] = compare_mismatch;
    dispatch[SPACE][MEOL] = compare_mismatch;
    dispatch[NSPACE][MEOL] = compare_mismatch;
    dispatch[DIGIT][MEOL] = compare_mismatch;
    dispatch[NDIGIT][MEOL] = compare_mismatch;
    dispatch[BRANCH][MEOL] = compare_left_branch;
    dispatch[EXACT][MEOL] = compare_exact_multiline;
    dispatch[EXACTF][MEOL] = compare_exact_multiline;
    dispatch[NOTHING][MEOL] = compare_left_tail;
    dispatch[STAR][MEOL] = compare_mismatch;
    dispatch[PLUS][MEOL] = compare_left_plus;
    dispatch[CURLY][MEOL] = compare_left_curly;
    dispatch[CURLYM][MEOL] = compare_left_curly;
    dispatch[CURLYX][MEOL] = compare_left_curly;
    dispatch[WHILEM][MEOL] = compare_left_tail;
    dispatch[MINMOD][MEOL] = compare_left_tail;

    dispatch[SUCCEED][SEOL] = compare_left_tail;
    dispatch[EOL][SEOL] = compare_tails;
    dispatch[SEOL][SEOL] = compare_tails;
    dispatch[BRANCH][SEOL] = compare_left_branch;
    dispatch[NOTHING][SEOL] = compare_left_tail;
    dispatch[STAR][SEOL] = 0;
    dispatch[PLUS][SEOL] = compare_left_plus;
    dispatch[CURLY][SEOL] = compare_left_curly;
    dispatch[CURLYM][SEOL] = compare_left_curly;
    dispatch[CURLYX][SEOL] = compare_left_curly;
    dispatch[WHILEM][SEOL] = compare_left_tail;
    dispatch[MINMOD][SEOL] = compare_left_tail;

    dispatch[SUCCEED][BOUND] = compare_left_tail;
    dispatch[BOL][BOUND] = compare_bol_word;
    dispatch[MBOL][BOUND] = compare_bol_word;
    dispatch[SBOL][BOUND] = compare_bol_word;
    dispatch[BOUND][BOUND] = compare_tails;
    dispatch[NBOUND][BOUND] = compare_mismatch;
    dispatch[REG_ANY][BOUND] = compare_mismatch;
    dispatch[SANY][BOUND] = compare_mismatch;
    dispatch[ANYOF][BOUND] = compare_anyof_bound;
    dispatch[ALNUM][BOUND] = compare_next_nword;
    dispatch[NALNUM][BOUND] = compare_next_word;
    dispatch[SPACE][BOUND] = compare_next_word;
    dispatch[NSPACE][BOUND] = compare_mismatch;
    dispatch[DIGIT][BOUND] = compare_next_nword;
    dispatch[NDIGIT][BOUND] = compare_mismatch;
    dispatch[BRANCH][BOUND] = compare_left_branch;
    dispatch[EXACT][BOUND] = compare_exact_bound;
    dispatch[EXACTF][BOUND] = compare_exact_bound;
    dispatch[NOTHING][BOUND] = compare_left_tail;
    dispatch[WHILEM][BOUND] = compare_left_tail;
    dispatch[MINMOD][BOUND] = compare_left_tail;

    dispatch[SUCCEED][NBOUND] = compare_left_tail;
    dispatch[BOL][NBOUND] = compare_bol_nword;
    dispatch[MBOL][NBOUND] = compare_bol_nword;
    dispatch[SBOL][NBOUND] = compare_bol_nword;
    dispatch[BOUND][NBOUND] = compare_mismatch;
    dispatch[NBOUND][NBOUND] = compare_tails;
    dispatch[REG_ANY][NBOUND] = compare_mismatch;
    dispatch[SANY][NBOUND] = compare_mismatch;
    dispatch[ANYOF][NBOUND] = compare_anyof_nbound;
    dispatch[ALNUM][NBOUND] = compare_next_word;
    dispatch[NALNUM][NBOUND] = compare_next_nword;
    dispatch[SPACE][NBOUND] = compare_next_nword;
    dispatch[NSPACE][NBOUND] = compare_mismatch;
    dispatch[DIGIT][NBOUND] = compare_next_word;
    dispatch[NDIGIT][NBOUND] = compare_mismatch;
    dispatch[BRANCH][NBOUND] = compare_left_branch;
    dispatch[EXACT][NBOUND] = compare_exact_nbound;
    dispatch[EXACTF][NBOUND] = compare_exact_nbound;
    dispatch[NOTHING][NBOUND] = compare_left_tail;
    dispatch[WHILEM][NBOUND] = compare_left_tail;
    dispatch[MINMOD][NBOUND] = compare_left_tail;

    dispatch[SUCCEED][REG_ANY] = compare_left_tail;
    dispatch[BOL][REG_ANY] = compare_bol;
    dispatch[MBOL][REG_ANY] = compare_bol;
    dispatch[SBOL][REG_ANY] = compare_bol;
    dispatch[BOUND][REG_ANY] = compare_mismatch;
    dispatch[NBOUND][REG_ANY] = compare_mismatch;
    dispatch[REG_ANY][REG_ANY] = compare_tails;
    dispatch[SANY][REG_ANY] = compare_mismatch;
    dispatch[ANYOF][REG_ANY] = compare_anyof_reg_any;
    dispatch[ALNUM][REG_ANY] = compare_tails;
    dispatch[NALNUM][REG_ANY] = compare_mismatch;
    dispatch[SPACE][REG_ANY] = compare_mismatch;
    dispatch[NSPACE][REG_ANY] = compare_tails;
    dispatch[DIGIT][REG_ANY] = compare_tails;
    dispatch[NDIGIT][REG_ANY] = compare_mismatch;
    dispatch[BRANCH][REG_ANY] = compare_left_branch;
    dispatch[EXACT][REG_ANY] = compare_exact_reg_any;
    dispatch[EXACTF][REG_ANY] = compare_exact_reg_any;
    dispatch[NOTHING][REG_ANY] = compare_left_tail;
    dispatch[STAR][REG_ANY] = compare_mismatch;
    dispatch[PLUS][REG_ANY] = compare_left_plus;
    dispatch[CURLY][REG_ANY] = compare_left_curly;
    dispatch[CURLYM][REG_ANY] = compare_left_curly;
    dispatch[CURLYX][REG_ANY] = compare_left_curly;
    dispatch[WHILEM][REG_ANY] = compare_left_tail;
    dispatch[MINMOD][REG_ANY] = compare_left_tail;

    dispatch[SUCCEED][SANY] = compare_left_tail;
    dispatch[BOL][SANY] = compare_bol;
    dispatch[MBOL][SANY] = compare_bol;
    dispatch[SBOL][SANY] = compare_bol;
    dispatch[BOUND][SANY] = compare_mismatch;
    dispatch[NBOUND][SANY] = compare_mismatch;
    dispatch[REG_ANY][SANY] = compare_tails;
    dispatch[SANY][SANY] = compare_tails;
    dispatch[ANYOF][SANY] = compare_tails;
    dispatch[ALNUM][SANY] = compare_tails;
    dispatch[NALNUM][SANY] = compare_tails;
    dispatch[SPACE][SANY] = compare_tails;
    dispatch[NSPACE][SANY] = compare_tails;
    dispatch[DIGIT][SANY] = compare_tails;
    dispatch[NDIGIT][SANY] = compare_tails;
    dispatch[BRANCH][SANY] = compare_left_branch;
    dispatch[EXACT][SANY] = compare_tails;
    dispatch[EXACTF][SANY] = compare_tails;
    dispatch[NOTHING][SANY] = compare_left_tail;
    dispatch[STAR][SANY] = compare_mismatch;
    dispatch[PLUS][SANY] = compare_left_plus;
    dispatch[CURLY][SANY] = compare_left_curly;
    dispatch[CURLYM][SANY] = compare_left_curly;
    dispatch[CURLYX][SANY] = compare_left_curly;
    dispatch[WHILEM][SANY] = compare_left_tail;
    dispatch[MINMOD][SANY] = compare_left_tail;

    dispatch[SUCCEED][ANYOF] = compare_left_tail;
    dispatch[BOL][ANYOF] = compare_bol;
    dispatch[MBOL][ANYOF] = compare_bol;
    dispatch[SBOL][ANYOF] = compare_bol;
    dispatch[BOUND][ANYOF] = compare_mismatch;
    dispatch[NBOUND][ANYOF] = compare_mismatch;
    dispatch[REG_ANY][ANYOF] = compare_reg_any_anyof;
    dispatch[SANY][ANYOF] = compare_mismatch;
    dispatch[ANYOF][ANYOF] = compare_anyof_anyof;
    dispatch[ALNUM][ANYOF] = compare_alnum_anyof;
    dispatch[NALNUM][ANYOF] = compare_nalnum_anyof;
    dispatch[SPACE][ANYOF] = compare_space_anyof;
    dispatch[NSPACE][ANYOF] = compare_nspace_anyof;
    dispatch[DIGIT][ANYOF] = compare_digit_anyof;
    dispatch[NDIGIT][ANYOF] = compare_ndigit_anyof;
    dispatch[BRANCH][ANYOF] = compare_left_branch;
    dispatch[EXACT][ANYOF] = compare_exact_anyof;
    dispatch[EXACTF][ANYOF] = compare_exactf_anyof;
    dispatch[NOTHING][ANYOF] = compare_left_tail;
    dispatch[STAR][ANYOF] = compare_mismatch;
    dispatch[PLUS][ANYOF] = compare_left_plus;
    dispatch[CURLY][ANYOF] = compare_left_curly;
    dispatch[CURLYM][ANYOF] = compare_left_curly;
    dispatch[CURLYX][ANYOF] = compare_left_curly;
    dispatch[WHILEM][ANYOF] = compare_left_tail;
    dispatch[MINMOD][ANYOF] = compare_left_tail;

    dispatch[SUCCEED][ALNUM] = compare_left_tail;
    dispatch[BOL][ALNUM] = compare_bol;
    dispatch[MBOL][ALNUM] = compare_bol;
    dispatch[SBOL][ALNUM] = compare_bol;
    dispatch[BOUND][ALNUM] = compare_mismatch;
    dispatch[NBOUND][ALNUM] = compare_mismatch;
    dispatch[REG_ANY][ALNUM] = compare_mismatch;
    dispatch[SANY][ALNUM] = compare_mismatch;
    dispatch[ANYOF][ALNUM] = compare_anyof_alnum;
    dispatch[ALNUM][ALNUM] = compare_tails;
    dispatch[NALNUM][ALNUM] = compare_mismatch;
    dispatch[SPACE][ALNUM] = compare_mismatch;
    dispatch[NSPACE][ALNUM] = compare_mismatch;
    dispatch[DIGIT][ALNUM] = compare_tails;
    dispatch[NDIGIT][ALNUM] = compare_mismatch;
    dispatch[BRANCH][ALNUM] = compare_left_branch;
    dispatch[EXACT][ALNUM] = compare_exact_alnum;
    dispatch[EXACTF][ALNUM] = compare_exact_alnum;
    dispatch[NOTHING][ALNUM] = compare_left_tail;
    dispatch[STAR][ALNUM] = compare_mismatch;
    dispatch[PLUS][ALNUM] = compare_left_plus;
    dispatch[CURLY][ALNUM] = compare_left_curly;
    dispatch[CURLYM][ALNUM] = compare_left_curly;
    dispatch[CURLYX][ALNUM] = compare_left_curly;
    dispatch[WHILEM][ALNUM] = compare_left_tail;
    dispatch[MINMOD][ALNUM] = compare_left_tail;

    dispatch[SUCCEED][NALNUM] = compare_left_tail;
    dispatch[BOL][NALNUM] = compare_bol;
    dispatch[MBOL][NALNUM] = compare_bol;
    dispatch[SBOL][NALNUM] = compare_bol;
    dispatch[BOUND][NALNUM] = compare_mismatch;
    dispatch[NBOUND][NALNUM] = compare_mismatch;
    dispatch[REG_ANY][NALNUM] = compare_mismatch;
    dispatch[SANY][NALNUM] = compare_mismatch;
    dispatch[ANYOF][NALNUM] = compare_anyof_nalnum;
    dispatch[ALNUM][NALNUM] = compare_mismatch;
    dispatch[NALNUM][NALNUM] = compare_tails;
    dispatch[SPACE][NALNUM] = compare_tails;
    dispatch[NSPACE][NALNUM] = compare_mismatch;
    dispatch[DIGIT][NALNUM] = compare_mismatch;
    dispatch[NDIGIT][NALNUM] = compare_mismatch;
    dispatch[BRANCH][NALNUM] = compare_left_branch;
    dispatch[EXACT][NALNUM] = compare_exact_nalnum;
    dispatch[EXACTF][NALNUM] = compare_exact_nalnum;
    dispatch[NOTHING][NALNUM] = compare_left_tail;
    dispatch[STAR][NALNUM] = compare_mismatch;
    dispatch[PLUS][NALNUM] = compare_left_plus;
    dispatch[CURLY][NALNUM] = compare_left_curly;
    dispatch[CURLYM][NALNUM] = compare_left_curly;
    dispatch[CURLYX][NALNUM] = compare_left_curly;
    dispatch[WHILEM][NALNUM] = compare_left_tail;
    dispatch[MINMOD][NALNUM] = compare_left_tail;

    dispatch[SUCCEED][SPACE] = compare_left_tail;
    dispatch[BOL][SPACE] = compare_bol;
    dispatch[MBOL][SPACE] = compare_bol;
    dispatch[SBOL][SPACE] = compare_bol;
    dispatch[BOUND][SPACE] = compare_mismatch;
    dispatch[NBOUND][SPACE] = compare_mismatch;
    dispatch[REG_ANY][SPACE] = compare_mismatch;
    dispatch[SANY][SPACE] = compare_mismatch;
    dispatch[ANYOF][SPACE] = compare_anyof_space;
    dispatch[ALNUM][SPACE] = compare_mismatch;
    dispatch[NALNUM][SPACE] = compare_mismatch;
    dispatch[SPACE][SPACE] = compare_tails;
    dispatch[NSPACE][SPACE] = compare_mismatch;
    dispatch[DIGIT][SPACE] = compare_mismatch;
    dispatch[NDIGIT][SPACE] = compare_mismatch;
    dispatch[BRANCH][SPACE] = compare_left_branch;
    dispatch[EXACT][SPACE] = compare_exact_space;
    dispatch[EXACTF][SPACE] = compare_exact_space;
    dispatch[NOTHING][SPACE] = compare_left_tail;
    dispatch[STAR][SPACE] = compare_mismatch;
    dispatch[PLUS][SPACE] = compare_left_plus;
    dispatch[CURLY][SPACE] = compare_left_curly;
    dispatch[CURLYM][SPACE] = compare_left_curly;
    dispatch[CURLYX][SPACE] = compare_left_curly;
    dispatch[WHILEM][SPACE] = compare_left_tail;
    dispatch[MINMOD][SPACE] = compare_left_tail;

    dispatch[SUCCEED][NSPACE] = compare_left_tail;
    dispatch[BOL][NSPACE] = compare_bol;
    dispatch[MBOL][NSPACE] = compare_bol;
    dispatch[SBOL][NSPACE] = compare_bol;
    dispatch[BOUND][NSPACE] = compare_mismatch;
    dispatch[NBOUND][NSPACE] = compare_mismatch;
    dispatch[REG_ANY][NSPACE] = compare_mismatch;
    dispatch[SANY][NSPACE] = compare_mismatch;
    dispatch[ANYOF][NSPACE] = compare_anyof_nspace;
    dispatch[ALNUM][NSPACE] = compare_tails;
    dispatch[NALNUM][NSPACE] = compare_mismatch;
    dispatch[SPACE][NSPACE] = compare_mismatch;
    dispatch[NSPACE][NSPACE] = compare_tails;
    dispatch[DIGIT][NSPACE] = compare_tails;
    dispatch[NDIGIT][NSPACE] = compare_mismatch;
    dispatch[BRANCH][NSPACE] = compare_left_branch;
    dispatch[EXACT][NSPACE] = compare_exact_nspace;
    dispatch[EXACTF][NSPACE] = compare_exact_nspace;
    dispatch[NOTHING][NSPACE] = compare_left_tail;
    dispatch[STAR][NSPACE] = compare_mismatch;
    dispatch[PLUS][NSPACE] = compare_left_plus;
    dispatch[CURLY][NSPACE] = compare_left_curly;
    dispatch[CURLYM][NSPACE] = compare_left_curly;
    dispatch[CURLYX][NSPACE] = compare_left_curly;
    dispatch[WHILEM][NSPACE] = compare_left_tail;
    dispatch[MINMOD][NSPACE] = compare_left_tail;

    dispatch[SUCCEED][DIGIT] = compare_left_tail;
    dispatch[BOL][DIGIT] = compare_bol;
    dispatch[MBOL][DIGIT] = compare_bol;
    dispatch[SBOL][DIGIT] = compare_bol;
    dispatch[BOUND][DIGIT] = compare_mismatch;
    dispatch[NBOUND][DIGIT] = compare_mismatch;
    dispatch[REG_ANY][DIGIT] = compare_mismatch;
    dispatch[SANY][DIGIT] = compare_mismatch;
    dispatch[ANYOF][DIGIT] = compare_anyof_digit;
    dispatch[ALNUM][DIGIT] = compare_mismatch;
    dispatch[NALNUM][DIGIT] = compare_mismatch;
    dispatch[SPACE][DIGIT] = compare_mismatch;
    dispatch[NSPACE][DIGIT] = compare_mismatch;
    dispatch[DIGIT][DIGIT] = compare_tails;
    dispatch[NDIGIT][DIGIT] = compare_mismatch;
    dispatch[BRANCH][DIGIT] = compare_left_branch;
    dispatch[EXACT][DIGIT] = compare_exact_digit;
    dispatch[EXACTF][DIGIT] = compare_exact_digit;
    dispatch[NOTHING][DIGIT] = compare_left_tail;
    dispatch[STAR][DIGIT] = compare_mismatch;
    dispatch[PLUS][DIGIT] = compare_left_plus;
    dispatch[CURLY][DIGIT] = compare_left_curly;
    dispatch[CURLYM][DIGIT] = compare_left_curly;
    dispatch[CURLYX][DIGIT] = compare_left_curly;
    dispatch[WHILEM][DIGIT] = compare_left_tail;
    dispatch[MINMOD][DIGIT] = compare_left_tail;

    dispatch[SUCCEED][NDIGIT] = compare_left_tail;
    dispatch[BOL][NDIGIT] = compare_bol;
    dispatch[MBOL][NDIGIT] = compare_bol;
    dispatch[SBOL][NDIGIT] = compare_bol;
    dispatch[BOUND][NDIGIT] = compare_mismatch;
    dispatch[NBOUND][NDIGIT] = compare_mismatch;
    dispatch[REG_ANY][NDIGIT] = compare_mismatch;
    dispatch[SANY][NDIGIT] = compare_mismatch;
    dispatch[ANYOF][NDIGIT] = compare_anyof_ndigit;
    dispatch[ALNUM][NDIGIT] = compare_mismatch;
    dispatch[NALNUM][NDIGIT] = compare_tails;
    dispatch[SPACE][NDIGIT] = compare_tails;
    dispatch[NSPACE][NDIGIT] = compare_mismatch;
    dispatch[DIGIT][NDIGIT] = compare_mismatch;
    dispatch[NDIGIT][NDIGIT] = compare_tails;
    dispatch[BRANCH][NDIGIT] = compare_left_branch;
    dispatch[EXACT][NDIGIT] = compare_exact_ndigit;
    dispatch[EXACTF][NDIGIT] = compare_exact_ndigit;
    dispatch[NOTHING][NDIGIT] = compare_left_tail;
    dispatch[STAR][NDIGIT] = compare_mismatch;
    dispatch[PLUS][NDIGIT] = compare_left_plus;
    dispatch[CURLY][NDIGIT] = compare_left_curly;
    dispatch[CURLYM][NDIGIT] = compare_left_curly;
    dispatch[CURLYX][NDIGIT] = compare_left_curly;
    dispatch[WHILEM][NDIGIT] = compare_left_tail;
    dispatch[MINMOD][NDIGIT] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][BRANCH] = compare_right_branch;
    }

    dispatch[SUCCEED][BRANCH] = compare_left_tail;
    dispatch[ANYOF][BRANCH] = compare_anyof_branch;
    dispatch[BRANCH][BRANCH] = compare_left_branch;
    dispatch[NOTHING][BRANCH] = compare_left_tail;
    dispatch[WHILEM][BRANCH] = compare_left_tail;
    dispatch[MINMOD][BRANCH] = compare_left_tail;

    dispatch[SUCCEED][EXACT] = compare_left_tail;
    dispatch[BOL][EXACT] = compare_bol;
    dispatch[MBOL][EXACT] = compare_bol;
    dispatch[SBOL][EXACT] = compare_bol;
    dispatch[BOUND][EXACT] = compare_mismatch;
    dispatch[NBOUND][EXACT] = compare_mismatch;
    dispatch[REG_ANY][EXACT] = compare_mismatch;
    dispatch[SANY][EXACT] = compare_mismatch;
    dispatch[ANYOF][EXACT] = compare_anyof_exact;
    dispatch[ALNUM][EXACT] = compare_mismatch;
    dispatch[NALNUM][EXACT] = compare_mismatch;
    dispatch[SPACE][EXACT] = compare_mismatch;
    dispatch[NSPACE][EXACT] = compare_mismatch;
    dispatch[DIGIT][EXACT] = compare_mismatch;
    dispatch[NDIGIT][EXACT] = compare_mismatch;
    dispatch[BRANCH][EXACT] = compare_left_branch;
    dispatch[EXACT][EXACT] = compare_exact_exact;
    dispatch[EXACTF][EXACT] = compare_exactf_exact;
    dispatch[NOTHING][EXACT] = compare_left_tail;
    dispatch[STAR][EXACT] = compare_mismatch;
    dispatch[PLUS][EXACT] = compare_left_plus;
    dispatch[CURLY][EXACT] = compare_left_curly;
    dispatch[CURLYM][EXACT] = compare_left_curly;
    dispatch[CURLYX][EXACT] = compare_left_curly;
    dispatch[WHILEM][EXACT] = compare_left_tail;
    dispatch[MINMOD][EXACT] = compare_left_tail;

    dispatch[SUCCEED][EXACTF] = compare_left_tail;
    dispatch[BOL][EXACTF] = compare_bol;
    dispatch[MBOL][EXACTF] = compare_bol;
    dispatch[SBOL][EXACTF] = compare_bol;
    dispatch[BOUND][EXACTF] = compare_mismatch;
    dispatch[NBOUND][EXACTF] = compare_mismatch;
    dispatch[REG_ANY][EXACTF] = compare_mismatch;
    dispatch[SANY][EXACTF] = compare_mismatch;
    dispatch[ANYOF][EXACTF] = compare_anyof_exactf;
    dispatch[ALNUM][EXACTF] = compare_mismatch;
    dispatch[NALNUM][EXACTF] = compare_mismatch;
    dispatch[SPACE][EXACTF] = compare_mismatch;
    dispatch[NSPACE][EXACTF] = compare_mismatch;
    dispatch[DIGIT][EXACTF] = compare_mismatch;
    dispatch[NDIGIT][EXACTF] = compare_mismatch;
    dispatch[BRANCH][EXACTF] = compare_left_branch;
    dispatch[EXACT][EXACTF] = compare_exact_exactf;
    dispatch[EXACTF][EXACTF] = compare_exactf_exactf;
    dispatch[NOTHING][EXACTF] = compare_left_tail;
    dispatch[STAR][EXACTF] = compare_mismatch;
    dispatch[PLUS][EXACTF] = compare_left_plus;
    dispatch[CURLY][EXACTF] = compare_left_curly;
    dispatch[CURLYM][EXACTF] = compare_left_curly;
    dispatch[CURLYX][EXACTF] = compare_left_curly;
    dispatch[WHILEM][EXACTF] = compare_left_tail;
    dispatch[MINMOD][EXACTF] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][NOTHING] = compare_next;
    }

    dispatch[SUCCEED][NOTHING] = compare_tails;
    dispatch[NOTHING][NOTHING] = compare_tails;
    dispatch[WHILEM][NOTHING] = compare_tails;
    dispatch[MINMOD][NOTHING] = compare_tails;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][STAR] = compare_right_star;
    }

    dispatch[SUCCEED][STAR] = compare_left_tail;
    dispatch[EOL][STAR] = compare_tails;
    dispatch[MEOL][STAR] = compare_tails;
    dispatch[SEOL][STAR] = compare_tails;
    dispatch[NOTHING][STAR] = compare_left_tail;
    dispatch[STAR][STAR] = compare_repeat_repeat;
    dispatch[PLUS][STAR] = compare_repeat_repeat;
    dispatch[CURLY][STAR] = compare_curly_star;
    dispatch[CURLYM][STAR] = compare_curly_star;
    dispatch[CURLYX][STAR] = compare_curly_star;
    dispatch[WHILEM][STAR] = compare_left_tail;
    dispatch[MINMOD][STAR] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][PLUS] = compare_right_plus;
    }

    dispatch[SUCCEED][PLUS] = compare_left_tail;
    dispatch[NOTHING][PLUS] = compare_left_tail;
    dispatch[PLUS][PLUS] = compare_repeat_repeat;
    dispatch[CURLY][PLUS] = compare_curly_plus;
    dispatch[CURLYM][PLUS] = compare_curly_plus;
    dispatch[CURLYX][PLUS] = compare_curly_plus;
    dispatch[WHILEM][PLUS] = compare_left_tail;
    dispatch[MINMOD][PLUS] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][CURLY] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLY] = compare_left_tail;
    dispatch[NOTHING][CURLY] = compare_left_tail;
    dispatch[PLUS][CURLY] = compare_plus_curly;
    dispatch[CURLY][CURLY] = compare_curly_curly;
    dispatch[CURLYM][CURLY] = compare_curly_curly;
    dispatch[CURLYX][CURLY] = compare_curly_curly;
    dispatch[WHILEM][CURLY] = compare_left_tail;
    dispatch[MINMOD][CURLY] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][CURLYM] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLYM] = compare_left_tail;
    dispatch[NOTHING][CURLYM] = compare_left_tail;
    dispatch[PLUS][CURLYM] = compare_plus_curly;
    dispatch[CURLY][CURLYM] = compare_curly_curly;
    dispatch[CURLYM][CURLYM] = compare_curly_curly;
    dispatch[CURLYX][CURLYM] = compare_curly_curly;
    dispatch[WHILEM][CURLYM] = compare_left_tail;
    dispatch[MINMOD][CURLYM] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][CURLYX] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLYX] = compare_left_tail;
    dispatch[NOTHING][CURLYX] = compare_left_tail;
    dispatch[PLUS][CURLYX] = compare_plus_curly;
    dispatch[CURLY][CURLYX] = compare_curly_curly;
    dispatch[CURLYM][CURLYX] = compare_curly_curly;
    dispatch[CURLYX][CURLYX] = compare_curly_curly;
    dispatch[WHILEM][CURLYX] = compare_left_tail;
    dispatch[MINMOD][CURLYX] = compare_left_tail;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][WHILEM] = compare_next;
    }

    dispatch[SUCCEED][WHILEM] = compare_tails;
    dispatch[NOTHING][WHILEM] = compare_tails;
    dispatch[WHILEM][WHILEM] = compare_tails;
    dispatch[MINMOD][WHILEM] = compare_tails;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][MINMOD] = compare_next;
    }

    dispatch[SUCCEED][MINMOD] = compare_tails;
    dispatch[NOTHING][MINMOD] = compare_tails;
    dispatch[WHILEM][MINMOD] = compare_tails;
    dispatch[MINMOD][MINMOD] = compare_tails;
}
