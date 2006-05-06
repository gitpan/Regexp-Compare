#include "engine.h"
#include "regnodes.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

#define SIZEOF_ARRAY(a) (sizeof(a) / sizeof(a[0]))

#define TOLOWER(c) ((((c) >= 'A') && ((c) <= 'Z')) ? ((c) - 'A' + 'a') : (c))

#define LETTER_COUNT ('z' - 'a' + 1)

#define INFINITE_COUNT 32767

typedef struct
{
    regnode *rn;
    int spent;
} Arrow;

#define GET_LITERAL(a) (((char *)((a)->rn + 1)) + (a)->spent)
#define GET_BITMAP(a) ((unsigned char *)((a)->rn + 2))

typedef int (*FCompare)(int, Arrow *, Arrow *);

typedef struct
{
    int offs;
    unsigned char mask;
} BitFlag;

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

/* isspace for C locale */
static char whitespace_expl[] = { ' ', '\f', '\n', '\r', '\t', '\v' };

static ByteClass whitespace;

static char digit_expl[10];

static ByteClass digit;

static char ndot_expl[] = { '\n' };

static ByteClass ndot;

static char alphanumeric_expl[11 + 2 * LETTER_COUNT];

static ByteClass alphanumeric;

static unsigned char alphanumeric_classes[OPTIMIZED];
static unsigned char non_alphanumeric_classes[OPTIMIZED];

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
    *unf = ((c >= 'A') && (c <= 'Z')) ? c - 'A' + 'a' : c;
    unf[1] = ((*unf >= 'a') && (*unf <= 'z')) ? *unf - 'a' + 'A' : *unf;
}

static int get_size(regnode *rn)
{
    regnode *e = rn;

    while (e->type != END)
    {
        if (!e->next_off)
	{
	    rc_error = "Zero offset";
	    return -1;
	}

        e += e->next_off;
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

static int ensure_offset(regnode *p)
{
    if (!p->next_off)
    {
        if ((p->type == EXACT) && (p->flags == 1))
	{
	    p->next_off = 2;
	}
	else if ((p->type == REG_ANY) || (p->type == SANY) ||
		 (p->type == ALNUM) || (p->type == NALNUM) ||
		 (p->type == SPACE) || (p->type == NSPACE) ||
		 (p->type == DIGIT) || (p->type == NDIGIT))
	{
	    p->next_off = 1;  
	}
	else
	{
	    rc_error = "Offset not set";
	    return -1;
	}
    }

    return 1;
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

    if (ensure_offset(alt) <= 0)
    {
        free(alt);
	return 0;
    }

    return alt;
}

static int bump_exact(Arrow *a)
{
    assert((a->rn->type == EXACT) || (a->rn->type == EXACTF));

    if (!a->rn->next_off)
    {
        rc_error = "Node has zero offset";
	return -1;
    }

    if (++(a->spent) >= a->rn->flags)
    {
	a->spent = 0;
	a->rn += a->rn->next_off;
    }

    return 1;
}

static int bump_regular(Arrow *a)
{
    int off;

    assert(a->rn->type != END);
    assert(a->rn->type != EXACT);
    assert(a->rn->type != EXACTF);
    assert(!a->spent);

    off = a->rn->next_off; 
    if (!off)
    {
	if (a->rn->type == SUCCEED)
	{
	    off = 1;
	}
	else
	{
	    rc_error = "Node with zero offset";
	    return -1;
	}
    }

    a->rn += off;
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

    end = strchr(rs, '\0');
    rx = pregcomp(rs, end, pm);
    if (!rx)
    {
        safefree(pm);
	croak("Cannot compile regexp");
    }

    safefree(pm);
    return rx;
}

void rc_regfree(void *rx)
{
    if (rx)
    {
        pregfree(rx);
    }
}

static int compare_tails(Arrow *a1, Arrow *a2)
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

    return compare(1, &tail1, &tail2);
}

static int compare_regular_tails(int dummy, Arrow *a1, Arrow *a2)
{
    return compare_tails(a1, a2);
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

static int compare_bol(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == BOL) || (a1->rn->type == MBOL) ||
	(a1->rn->type == SBOL));

    if (anchored)
    {
        return 0;
    }
    else
    {
	if (bump_regular(a1) <= 0)
	{
	    return -1;
	}

	return compare(1, a1, a2);
    }
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

    return compare_tails(a1, a2);
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

    bitmap = (unsigned char *)(a2->rn + 2); /* skip "arg1" */
    for (i = 0; i < left->expl_size; ++i)
    {
      init_bit_flag(&bf, (unsigned char)left->expl[i]);
	if (!(bitmap[bf.offs] & bf.mask))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
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

    assert(a1->rn->type == EXACT);
    assert(a2->rn->type == EXACT);

    q1 = GET_LITERAL(a1);
    q2 = GET_LITERAL(a2);

    /* fprintf(stderr, "compare_exact_exact(%d, %c, %c)\n", anchored,
     *q1, *q2); */

    if (*q1 != *q2)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
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

    return compare_tails(a1, a2);
}

static int compare_left_branch(int anchored, Arrow *a1, Arrow *a2)
{
    int rv;
    regnode *t, *p1;
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
	    return compare_mismatch(anchored, a1, a2);
	}

	p1 += p1->next_off;
    }

    a1->rn = p1;
    a1->spent = 0;

    t = a2->rn;
    while (t->type != END)
    {
	t += t->next_off;
    }

    a2->rn = t;
    a2->spent = 0;

    return 1;
}

static int compare_anyof_branch(int anchored, Arrow *a1, Arrow *a2)
{
    unsigned char *bitmap;
    regnode *alt, *t1;
    Arrow left, right;
    int i, j, power, rv, sz;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == BRANCH);

    bitmap = (unsigned char *)(a1->rn + 2);
    t1 = a1->rn + a1->rn->next_off;
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
    regnode *p2, *alt;
    Arrow left, right;
    int sz, rv;

    p2 = a2->rn;
    assert(p2->type == STAR);

    sz = get_size(p2);
    if (sz < 0)
    {
	return sz;
    }

    left.rn = a1->rn;
    left.spent = a1->spent;

    right.rn = p2 + p2->next_off;
    right.spent = 0;

    rv = compare(anchored, &left, &right);
    if (rv < 0)
    {
	return rv;
    }

    if (rv == 0)
    {
	alt = (regnode *)malloc(sizeof(regnode) * sz);
	if (!alt)
	{
	    rc_error = "Couldn't allocate memory for star";
	    return -1;
	}

        memcpy(alt, p2, sizeof(regnode) * sz);

	rv = ensure_offset(alt + 1);
	if (rv < 0)
	{
	    free(alt);
	    return rv;
	}

	right.rn = alt + 1;
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

	right.rn = alt;
	right.spent = 0;

	rv = compare_right_star(1, a1, &right);
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

static int compare_repeat_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *alt1, *alt2;
    Arrow left, right;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert((p1->type == PLUS) || (p1->type == STAR));
    p2 = a2->rn;
    assert(p2->type == STAR);

    sz1 = get_size(p1);
    if (sz1 <= 0)
    {
	return -1;
    }

    alt1 = alloc_alt(p1 + 1, sz1 - 1);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    sz2 = get_size(p2);
    if (sz2 <= 0)
    {
	return -1;
    }

    alt2 = alloc_alt(p2 + 1, sz2 - 1);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);
    free(alt1);
    free(alt2);
    return rv;
}

static int compare_right_curly_from_zero(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2, *alt;
    short n, *cnt;
    Arrow left, right;
    int sz, rv;

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

    right.rn = p2 + p2->next_off;
    right.spent = 0;

    rv = compare(anchored, &left, &right);
    if (rv < 0)
    {
	return rv;
    }

    if (rv == 0)
    {
	alt = (regnode *)malloc(sizeof(regnode) * sz);
	if (!alt)
	{
	    rc_error = "Couldn't allocate memory for curly";
	    return -1;
	}

        memcpy(alt, p2, sizeof(regnode) * sz);

	rv = ensure_offset(alt + 2);
	if (rv < 0)
	{
	    free(alt);
	    return rv;
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
    regnode *p1, *alt;
    Arrow left, right;
    int sz, rv, end_off;
    unsigned char orig_type;

    p1 = a1->rn;
    assert(p1->type == PLUS);

    sz = get_size(p1);
    if (sz <= 0)
    {
	return -1;
    }

    alt = alloc_alt(p1 + 1, sz - 1);
    if (!alt)
    {
	return -1;
    }

    if (anchored)
    {
        right.rn = a2->rn;
        right.spent = a2->spent;
	if (bump_with_check(&right) <= 0)
	{
	    free(alt);
	    return -1;
	}

	/* FIXME: ignoring the possibility of NOTHING and SUCCEED
	   nodes */
	if (right.rn->type != END)
	{
	    /* repeat with a tail after it can be more strict than a
	       fixed-length match only if the tail is at least as
	       strict as the repeated regexp */
	    left.rn = a1->rn;
	    left.spent = a1->spent;
	    if (bump_with_check(&left) <= 0)
	    {
		free(alt);
		return -1;
	    }

	    end_off = p1->next_off - 1;
	    orig_type = alt[end_off].type;
	    alt[end_off].type = END;

	    right.rn = alt;
	    right.spent = 0;

	    rv = compare(1, &left, &right);
	    if (rv <= 0)
	    {
		free(alt);
		return rv;
	    }

	    alt[end_off].type = orig_type;
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
    regnode *p2, *alt;
    Arrow right;
    int sz, rv;

    p2 = a2->rn;
    assert(p2->type == PLUS);

    /* fprintf(stderr, "enter compare_right_plus\n"); */

    sz = get_size(p2);
    if (sz <= 0)
    {
	return -1;
    }

    /* fprintf(stderr, "sz = %d\n", sz); */

    alt = (regnode *)malloc(sizeof(regnode) * sz);
    if (!alt)
    {
        rc_error = "Couldn't allocate memory for right plus";
	return -1;
    }

    memcpy(alt, p2, sizeof(regnode) * sz);

    rv = ensure_offset(alt + 1);
    if (rv < 0)
    {
        free(alt);
	return rv;
    }

    right.rn = alt + 1;
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

    alt->type = STAR;
    right.rn = alt;
    right.spent = 0;

    rv = compare_right_star(1, a1, &right);
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

static int compare_next(int anchored, Arrow *a1, Arrow *a2)
{
    if (bump_regular(a2) <= 0)
    {
        return -1;
    }

    return compare(anchored, a1, a2);
}

static int compare_plus_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *alt1, *alt2;
    Arrow left, right;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert(p1->type == PLUS);
    p2 = a2->rn;
    assert(p2->type == PLUS);

    sz1 = get_size(p1);
    if (sz1 < 0)
    {
	return -1;
    }

    if (sz1 < 2)
    {
	rc_error = "Offset is too small";
	return -1;
    }

    alt1 = alloc_alt(p1 + 1, sz1 - 1);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    sz2 = get_size(p2);
    if (sz2 < 0)
    {
        free(alt1);
	return -1;
    }

    if (sz2 < 2)
    {
        free(alt1);
	rc_error = "Offset too small";
	return -1;
    }

    alt2 = alloc_alt(p2 + 1, sz2 - 1);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);

    free(alt1);
    free(alt2);
    return rv;
}

static int compare_curly_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *alt1, *alt2;
    Arrow left, right;
    short *cnt;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM));
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

    sz1 = get_size(p1);
    if (sz1 < 0)
    {
	return -1;
    }

    if (sz1 < 3)
    {
	rc_error = "Curly offset too small";
	return -1;
    }

    alt1 = alloc_alt(p1 + 2, sz1 - 2);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    sz2 = get_size(p2);
    if (sz2 < 0)
    {
        free(alt1);
	return -1;
    }

    if (sz2 < 2)
    {
        free(alt1);
	rc_error = "Plus offset too small";
	return -1;
    }

    alt2 = alloc_alt(p2 + 1, sz2 - 1);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);

    free(alt1);
    free(alt2);
    return rv;
}

static int compare_curly_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *alt1, *alt2;
    Arrow left, right;
    short *cnt;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM));
    p2 = a2->rn;
    assert(p2->type == STAR);

    sz1 = get_size(p1);
    if (sz1 < 0)
    {
	return -1;
    }

    if (sz1 < 2)
    {
	rc_error = "Curly offset too small";
	return -1;
    }

    alt1 = alloc_alt(p1 + 2, sz1 - 2);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    sz2 = get_size(p2);
    if (sz1 <= 0)
    {
        free(alt1);
	return -1;
    }

    alt2 = alloc_alt(p2 + 1, sz2 - 1);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);

    free(alt1);
    free(alt2);

    if (rv < 0)
    {
	return rv;
    }

    if (!rv)
    {
	rv = compare_next(anchored, a1, a2);
    }

    return rv;
}

static int compare_plus_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2, *e2, *alt1, *alt2;
    Arrow left, right;
    short *cnt;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert(p1->type == PLUS);
    p2 = a2->rn;
    assert((p2->type == CURLY) || (p2->type == CURLYM));

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

    sz1 = get_size(p1);
    if (sz1 <= 0)
    {
	return -1;
    }

    alt1 = alloc_alt(p1 + 1, sz1 - 1);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    if (p2->next_off < 2)
    {
	free(alt1);
	rc_error = "Curly offset too small";
	return -1;
    }

    e2 = p2 + p2->next_off;
    while (e2->type != END)
    {
        if (!e2->next_off)
	{
	    free(alt1);
	    rc_error = "Zero offset";
	    return -1;
	}

	if ((cnt[1] != INFINITE_COUNT) &&
	    ((e2->type != NOTHING) && (e2->type != SUCCEED)))
	{
	    free(alt1);
	    return compare_mismatch(anchored, a1, a2);	    
	}

        e2 += e2->next_off;
    }

    sz2 = p2->next_off + e2 - p2 - 1;
    alt2 = alloc_alt(p2 + 2, sz2);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);
    free(alt1);
    free(alt2);
    return (!rv && !cnt[0]) ? compare_next(anchored, a1, a2) : rv;
}

static int compare_left_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *alt;
    Arrow left, right;
    int sz, rv, end_off;
    unsigned char orig_type;
    short *cnt;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM));

    cnt = (short *)(p1 + 1);
    if (!cnt[0])
    {
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

    alt = alloc_alt(p1 + 2, sz - 2);
    if (!alt)
    {
        rc_error = "Couldn't allocate memory for left plus";
	return -1;
    }

    if (anchored && !((cnt[0] == 1) && (cnt[1] == 1)))
    {
        right.rn = a2->rn;
        right.spent = a2->spent;
	if (bump_with_check(&right) <= 0)
	{
	    free(alt);
	    return -1;
	}

	/* FIXME: ignoring the possibility of NOTHING and SUCCEED
	   nodes */
	if (right.rn->type != END)
	{
	    /* repeat with a tail after it can be more strict than a
	       fixed-length match only if the tail is at least as
	       strict as the repeated regexp */
	    left.rn = a1->rn;
	    left.spent = a1->spent;
	    if (bump_with_check(&left) <= 0)
	    {
		free(alt);
		return -1;
	    }

	    end_off = p1->next_off - 1;
	    orig_type = alt[end_off].type;
	    alt[end_off].type = END;

	    right.rn = alt;
	    right.spent = 0;

	    rv = compare(1, &left, &right);
	    if (rv <= 0)
	    {
		free(alt);
		return rv;
	    }

	    alt[end_off].type = orig_type;
	}
    }

    left.rn = alt;
    left.spent = 0;
    rv = compare(anchored, &left, a2);
    free(alt);
    return rv;
}

static int compare_right_curly(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p2, *alt;
    Arrow right;
    short m, *cnt;
    int sz, rv, nanch;

    p2 = a2->rn;

    m = *((short *)(p2 + 1));
    if (m < 0)
    {
	rc_error = "Curly has negative minimum";
	return -1;
    }

    /* fprintf(stderr, "compare_right_curly from %d\n", m); */

    nanch = anchored;

    if (m > 0)
    {
        sz = get_size(p2);
	if (sz < 0)
	{
	    return sz;
	}

	if (sz < 1)
	{
	    rc_error = "Right curly offset too small";
	    return -1;
	}

	alt = (regnode *)malloc(sizeof(regnode) * sz);
	if (!alt)
	{
	    rc_error = "Couldn't allocate memory for curly";
	    return -1;
	}

        memcpy(alt, p2, sizeof(regnode) * sz);

	rv = ensure_offset(alt + 2);
	if (rv < 0)
	{
	    free(alt);
	    return rv;
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

	/* strictly speaking, matching one repeat didn't *necessarily*
	   anchor the match, but we'll ignore such cases as
	   pathological */
	nanch = 1;

	cnt = (short *)(alt + 1);
	--cnt[0];
	if (cnt[1] < INFINITE_COUNT)
	{
	    --cnt[1];
	}

	if (cnt[1] > 0)
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
    regnode *p1, *p2, *e2, *alt1, *alt2;
    Arrow left, right;
    short *cnt1, *cnt2;
    int sz1, sz2, rv;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM));
    p2 = a2->rn;
    assert((p2->type == CURLY) || (p2->type == CURLYM));

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

    sz1 = get_size(p1);
    if (sz1 < 3)
    {
	rc_error = "Size too small";
	return -1;
    }

    alt1 = alloc_alt(p1 + 2, sz1 - 2);
    if (!alt1)
    {
	return -1;
    }

    left.rn = alt1;
    left.spent = 0;

    if (p2->next_off < 2)
    {
	free(alt1);
	rc_error = "Right curly offset too small";
	return -1;
    }

    e2 = p2 + p2->next_off;
    while (e2->type != END)
    {
        if (!e2->next_off)
	{
	    free(alt1);
	    rc_error = "Zero offset";
	    return -1;
	}

	if ((cnt1[1] > cnt2[1]) &&
	    ((e2->type != NOTHING) && (e2->type != SUCCEED)))
	{
	    free(alt1);
	    return compare_mismatch(anchored, a1, a2);	    
	}

        e2 += e2->next_off;
    }

    sz2 = p2->next_off + e2 - p2 - 1;
    alt2 = alloc_alt(p2 + 2, sz2);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    right.rn = alt2;
    right.spent = 0;

    rv = compare(1, &left, &right);
    free(alt1);
    free(alt2);
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
    int rv;

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

    rv = cmp(anchored, a1, a2);

    if (!rv)
    {
	rv = compare_mismatch(anchored, a1, a2);
    }

    /* fprintf(stderr, "compare returns %d\n", rv); */
    return rv;
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
    for (i = 0; i < 10; ++i)
    {
	alphanumeric_expl[wstart + i] = '0' + i;
    }

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

    memset(dispatch, 0, sizeof(FCompare) * OPTIMIZED * OPTIMIZED);

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][END] = success;
	dispatch[i][SUCCEED] = compare_next;
    }

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][BOL] = 0;
    }

    dispatch[BOL][BOL] = compare_regular_tails;
    dispatch[SBOL][BOL] = compare_regular_tails;
    dispatch[BRANCH][BOL] = compare_left_branch;
    dispatch[NOTHING][BOL] = compare_left_tail;
    dispatch[STAR][BOL] = compare_mismatch;
    dispatch[PLUS][BOL] = compare_left_plus;
    dispatch[CURLY][BOL] = compare_left_curly;
    dispatch[CURLYM][BOL] = compare_left_curly;

    dispatch[BOL][MBOL] = compare_regular_tails;
    dispatch[MBOL][MBOL] = compare_regular_tails;
    dispatch[SBOL][MBOL] = compare_regular_tails;
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

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][SBOL] = 0;
    }

    dispatch[BOL][SBOL] = compare_regular_tails;
    dispatch[SBOL][SBOL] = compare_regular_tails;
    dispatch[BRANCH][SBOL] = compare_left_branch;
    dispatch[NOTHING][SBOL] = compare_left_tail;
    dispatch[STAR][SBOL] = compare_mismatch;
    dispatch[PLUS][SBOL] = compare_left_plus;
    dispatch[CURLY][SBOL] = compare_left_curly;
    dispatch[CURLYM][SBOL] = compare_left_curly;

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][EOL] = 0;
    }

    dispatch[EOL][EOL] = compare_regular_tails;
    dispatch[SEOL][EOL] = compare_regular_tails;
    dispatch[BRANCH][EOL] = compare_left_branch;
    dispatch[NOTHING][EOL] = compare_left_tail;
    dispatch[STAR][EOL] = compare_mismatch;
    dispatch[PLUS][EOL] = compare_left_plus;
    dispatch[CURLY][EOL] = compare_left_curly;
    dispatch[CURLYM][EOL] = compare_left_curly;

    dispatch[EOL][MEOL] = compare_regular_tails;
    dispatch[MEOL][MEOL] = compare_regular_tails;
    dispatch[SEOL][MEOL] = compare_regular_tails;
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

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][SEOL] = 0;
    }

    dispatch[EOL][SEOL] = compare_regular_tails;
    dispatch[SEOL][SEOL] = compare_regular_tails;
    dispatch[BRANCH][SEOL] = compare_left_branch;
    dispatch[NOTHING][SEOL] = compare_left_tail;
    dispatch[STAR][SEOL] = 0;
    dispatch[PLUS][SEOL] = compare_left_plus;
    dispatch[CURLY][SEOL] = compare_left_curly;
    dispatch[CURLYM][SEOL] = compare_left_curly;

    dispatch[BOL][BOUND] = compare_bol_word;
    dispatch[MBOL][BOUND] = compare_bol_word;
    dispatch[SBOL][BOUND] = compare_bol_word;
    dispatch[BOUND][BOUND] = compare_regular_tails;
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

    dispatch[BOL][NBOUND] = compare_bol_nword;
    dispatch[MBOL][NBOUND] = compare_bol_nword;
    dispatch[SBOL][NBOUND] = compare_bol_nword;
    dispatch[BOUND][NBOUND] = compare_mismatch;
    dispatch[NBOUND][NBOUND] = compare_regular_tails;
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

    dispatch[BOL][REG_ANY] = compare_bol;
    dispatch[MBOL][REG_ANY] = compare_bol;
    dispatch[SBOL][REG_ANY] = compare_bol;
    dispatch[REG_ANY][REG_ANY] = compare_regular_tails;
    dispatch[SANY][REG_ANY] = compare_mismatch;
    dispatch[ANYOF][REG_ANY] = compare_anyof_reg_any;
    dispatch[ALNUM][REG_ANY] = compare_regular_tails;
    dispatch[NALNUM][REG_ANY] = compare_mismatch;
    dispatch[SPACE][REG_ANY] = compare_mismatch;
    dispatch[NSPACE][REG_ANY] = compare_regular_tails;
    dispatch[DIGIT][REG_ANY] = compare_regular_tails;
    dispatch[NDIGIT][REG_ANY] = compare_mismatch;
    dispatch[BRANCH][REG_ANY] = compare_left_branch;
    dispatch[EXACT][REG_ANY] = compare_exact_reg_any;
    dispatch[EXACTF][REG_ANY] = compare_exact_reg_any;
    dispatch[NOTHING][REG_ANY] = compare_left_tail;
    dispatch[STAR][REG_ANY] = compare_mismatch;
    dispatch[PLUS][REG_ANY] = compare_left_plus;
    dispatch[CURLY][REG_ANY] = compare_left_curly;
    dispatch[CURLYM][REG_ANY] = compare_left_curly;

    dispatch[BOL][SANY] = compare_bol;
    dispatch[MBOL][SANY] = compare_bol;
    dispatch[SBOL][SANY] = compare_bol;
    dispatch[REG_ANY][SANY] = compare_regular_tails;
    dispatch[SANY][SANY] = compare_regular_tails;
    dispatch[ANYOF][SANY] = compare_regular_tails;
    dispatch[ALNUM][SANY] = compare_regular_tails;
    dispatch[NALNUM][SANY] = compare_regular_tails;
    dispatch[SPACE][SANY] = compare_regular_tails;
    dispatch[NSPACE][SANY] = compare_regular_tails;
    dispatch[DIGIT][SANY] = compare_regular_tails;
    dispatch[NDIGIT][SANY] = compare_regular_tails;
    dispatch[BRANCH][SANY] = compare_left_branch;
    dispatch[EXACT][SANY] = compare_regular_tails;
    dispatch[EXACTF][SANY] = compare_regular_tails;
    dispatch[NOTHING][SANY] = compare_left_tail;
    dispatch[STAR][SANY] = compare_mismatch;
    dispatch[PLUS][SANY] = compare_left_plus;
    dispatch[CURLY][SANY] = compare_left_curly;
    dispatch[CURLYM][SANY] = compare_left_curly;

    dispatch[BOL][ANYOF] = compare_bol;
    dispatch[MBOL][ANYOF] = compare_bol;
    dispatch[SBOL][ANYOF] = compare_bol;
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

    dispatch[BOL][ALNUM] = compare_bol;
    dispatch[MBOL][ALNUM] = compare_bol;
    dispatch[SBOL][ALNUM] = compare_bol;
    dispatch[REG_ANY][ALNUM] = compare_mismatch;
    dispatch[SANY][ALNUM] = compare_mismatch;
    dispatch[ANYOF][ALNUM] = compare_anyof_alnum;
    dispatch[ALNUM][ALNUM] = compare_regular_tails;
    dispatch[NALNUM][ALNUM] = compare_mismatch;
    dispatch[SPACE][ALNUM] = compare_mismatch;
    dispatch[NSPACE][ALNUM] = compare_mismatch;
    dispatch[DIGIT][ALNUM] = compare_regular_tails;
    dispatch[NDIGIT][ALNUM] = compare_mismatch;
    dispatch[BRANCH][ALNUM] = compare_left_branch;
    dispatch[EXACT][ALNUM] = compare_exact_alnum;
    dispatch[EXACTF][ALNUM] = compare_exact_alnum;
    dispatch[NOTHING][ALNUM] = compare_left_tail;
    dispatch[STAR][ALNUM] = compare_mismatch;
    dispatch[PLUS][ALNUM] = compare_left_plus;
    dispatch[CURLY][ALNUM] = compare_left_curly;
    dispatch[CURLYM][ALNUM] = compare_left_curly;

    dispatch[BOL][NALNUM] = compare_bol;
    dispatch[MBOL][NALNUM] = compare_bol;
    dispatch[SBOL][NALNUM] = compare_bol;
    dispatch[REG_ANY][NALNUM] = compare_mismatch;
    dispatch[SANY][NALNUM] = compare_mismatch;
    dispatch[ANYOF][NALNUM] = compare_anyof_nalnum;
    dispatch[ALNUM][NALNUM] = compare_mismatch;
    dispatch[NALNUM][NALNUM] = compare_regular_tails;
    dispatch[SPACE][NALNUM] = compare_regular_tails;
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

    dispatch[BOL][SPACE] = compare_bol;
    dispatch[MBOL][SPACE] = compare_bol;
    dispatch[SBOL][SPACE] = compare_bol;
    dispatch[REG_ANY][SPACE] = compare_mismatch;
    dispatch[SANY][SPACE] = compare_mismatch;
    dispatch[ANYOF][SPACE] = compare_anyof_space;
    dispatch[ALNUM][SPACE] = compare_mismatch;
    dispatch[NALNUM][SPACE] = compare_mismatch;
    dispatch[SPACE][SPACE] = compare_regular_tails;
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

    dispatch[BOL][NSPACE] = compare_bol;
    dispatch[MBOL][NSPACE] = compare_bol;
    dispatch[SBOL][NSPACE] = compare_bol;
    dispatch[REG_ANY][NSPACE] = compare_mismatch;
    dispatch[SANY][NSPACE] = compare_mismatch;
    dispatch[ANYOF][NSPACE] = compare_anyof_nspace;
    dispatch[ALNUM][NSPACE] = compare_regular_tails;
    dispatch[NALNUM][NSPACE] = compare_mismatch;
    dispatch[SPACE][NSPACE] = compare_mismatch;
    dispatch[NSPACE][NSPACE] = compare_regular_tails;
    dispatch[DIGIT][NSPACE] = compare_regular_tails;
    dispatch[NDIGIT][NSPACE] = compare_mismatch;
    dispatch[BRANCH][NSPACE] = compare_left_branch;
    dispatch[EXACT][NSPACE] = compare_exact_nspace;
    dispatch[EXACTF][NSPACE] = compare_exact_nspace;
    dispatch[NOTHING][NSPACE] = compare_left_tail;
    dispatch[STAR][NSPACE] = compare_mismatch;
    dispatch[PLUS][NSPACE] = compare_left_plus;
    dispatch[CURLY][NSPACE] = compare_left_curly;
    dispatch[CURLYM][NSPACE] = compare_left_curly;

    dispatch[BOL][DIGIT] = compare_bol;
    dispatch[MBOL][DIGIT] = compare_bol;
    dispatch[SBOL][DIGIT] = compare_bol;
    dispatch[REG_ANY][DIGIT] = compare_mismatch;
    dispatch[SANY][DIGIT] = compare_mismatch;
    dispatch[ANYOF][DIGIT] = compare_anyof_digit;
    dispatch[ALNUM][DIGIT] = compare_mismatch;
    dispatch[NALNUM][DIGIT] = compare_mismatch;
    dispatch[SPACE][DIGIT] = compare_mismatch;
    dispatch[NSPACE][DIGIT] = compare_mismatch;
    dispatch[DIGIT][DIGIT] = compare_regular_tails;
    dispatch[NDIGIT][DIGIT] = compare_mismatch;
    dispatch[BRANCH][DIGIT] = compare_left_branch;
    dispatch[EXACT][DIGIT] = compare_exact_digit;
    dispatch[EXACTF][DIGIT] = compare_exact_digit;
    dispatch[NOTHING][DIGIT] = compare_left_tail;
    dispatch[STAR][DIGIT] = compare_mismatch;
    dispatch[PLUS][DIGIT] = compare_left_plus;
    dispatch[CURLY][DIGIT] = compare_left_curly;
    dispatch[CURLYM][DIGIT] = compare_left_curly;

    dispatch[BOL][NDIGIT] = compare_bol;
    dispatch[MBOL][NDIGIT] = compare_bol;
    dispatch[SBOL][NDIGIT] = compare_bol;
    dispatch[REG_ANY][NDIGIT] = compare_mismatch;
    dispatch[SANY][NDIGIT] = compare_mismatch;
    dispatch[ANYOF][NDIGIT] = compare_anyof_ndigit;
    dispatch[ALNUM][NDIGIT] = compare_mismatch;
    dispatch[NALNUM][NDIGIT] = compare_regular_tails;
    dispatch[SPACE][NDIGIT] = compare_regular_tails;
    dispatch[NSPACE][NDIGIT] = compare_mismatch;
    dispatch[DIGIT][NDIGIT] = compare_mismatch;
    dispatch[NDIGIT][NDIGIT] = compare_regular_tails;
    dispatch[BRANCH][NDIGIT] = compare_left_branch;
    dispatch[EXACT][NDIGIT] = compare_exact_ndigit;
    dispatch[EXACTF][NDIGIT] = compare_exact_ndigit;
    dispatch[NOTHING][NDIGIT] = compare_left_tail;
    dispatch[STAR][NDIGIT] = compare_mismatch;
    dispatch[PLUS][NDIGIT] = compare_left_plus;
    dispatch[CURLY][NDIGIT] = compare_left_curly;
    dispatch[CURLYM][NDIGIT] = compare_left_curly;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][BRANCH] = compare_right_branch;
    }

    dispatch[ANYOF][BRANCH] = compare_anyof_branch;
    dispatch[BRANCH][BRANCH] = compare_left_branch;
    dispatch[NOTHING][BRANCH] = compare_left_tail;

    dispatch[BOL][EXACT] = compare_bol;
    dispatch[MBOL][EXACT] = compare_bol;
    dispatch[SBOL][EXACT] = compare_bol;
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
    dispatch[EXACTF][EXACT] = compare_mismatch;
    dispatch[NOTHING][EXACT] = compare_left_tail;
    dispatch[STAR][EXACT] = compare_mismatch;
    dispatch[PLUS][EXACT] = compare_left_plus;
    dispatch[CURLY][EXACT] = compare_left_curly;
    dispatch[CURLYM][EXACT] = compare_left_curly;

    dispatch[BOL][EXACTF] = compare_bol;
    dispatch[MBOL][EXACTF] = compare_bol;
    dispatch[SBOL][EXACTF] = compare_bol;
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

    for (i = 0; i < OPTIMIZED; ++i)
    {
        dispatch[i][NOTHING] = compare_next;
    }

    dispatch[NOTHING][NOTHING] = compare_regular_tails;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][STAR] = compare_right_star;
    }

    dispatch[EOL][STAR] = compare_regular_tails;
    dispatch[MEOL][STAR] = compare_regular_tails;
    dispatch[SEOL][STAR] = compare_regular_tails;
    dispatch[NOTHING][STAR] = compare_left_tail;
    dispatch[STAR][STAR] = compare_repeat_star;
    dispatch[PLUS][STAR] = compare_repeat_star;
    dispatch[CURLY][STAR] = compare_curly_star;
    dispatch[CURLYM][STAR] = compare_curly_star;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][PLUS] = compare_right_plus;
    }

    dispatch[NOTHING][PLUS] = compare_left_tail;
    dispatch[PLUS][PLUS] = compare_plus_plus;
    dispatch[CURLY][PLUS] = compare_curly_plus;
    dispatch[CURLYM][PLUS] = compare_curly_plus;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][CURLY] = compare_right_curly;
    }

    dispatch[NOTHING][CURLY] = compare_left_tail;
    dispatch[PLUS][CURLY] = compare_plus_curly;
    dispatch[CURLY][CURLY] = compare_curly_curly;
    dispatch[CURLYM][CURLY] = compare_curly_curly;

    for (i = 0; i < OPTIMIZED; ++i)
    {
	dispatch[i][CURLYM] = compare_right_curly;
    }

    dispatch[NOTHING][CURLYM] = compare_left_tail;
    dispatch[PLUS][CURLYM] = compare_plus_curly;
    dispatch[CURLY][CURLYM] = compare_curly_curly;
    dispatch[CURLYM][CURLYM] = compare_curly_curly;
}
