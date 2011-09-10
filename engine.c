#include "engine.h"
#include "regnodes.h"
#include "regcomp.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

#define SIZEOF_ARRAY(a) (sizeof(a) / sizeof(a[0]))

#define TOLOWER(c) ((((c) >= 'A') && ((c) <= 'Z')) ? ((c) - 'A' + 'a') : (c))

#define LETTER_COUNT ('z' - 'a' + 1)

#define INFINITE_COUNT 32767

#define TYPE_COUNT (OPTIMIZED + 1)

#define ALNUM_BLOCK 0x0001
#define SPACE_BLOCK 0x0002
#define ALPHA_BLOCK 0x0004
#define NUMBER_BLOCK 0x0008
#define UPPER_BLOCK 0x0010
#define LOWER_BLOCK 0x0020

#define MIRROR_SHIFT 8
#define NOT_ALNUM_BLOCK (ALNUM_BLOCK << MIRROR_SHIFT)
#define NOT_SPACE_BLOCK (SPACE_BLOCK << MIRROR_SHIFT)
#define NOT_ALPHA_BLOCK (ALPHA_BLOCK << MIRROR_SHIFT)
#define NOT_NUMBER_BLOCK (NUMBER_BLOCK << MIRROR_SHIFT)
#define NOT_UPPER_BLOCK (UPPER_BLOCK << MIRROR_SHIFT)
#define NOT_LOWER_BLOCK (LOWER_BLOCK << MIRROR_SHIFT)

#define EVERY_BLOCK 0x3f3f

#define FORCED_BYTE 0x01
#define FORCED_CHAR 0x02
#define FORCED_MISMATCH (FORCED_BYTE | FORCED_CHAR)

#define MIRROR_BLOCK(b) ((((b) & 0xff) << MIRROR_SHIFT) | ((b) >> MIRROR_SHIFT))

/* Regexp terms are normally regnodes, except for EXACT (and EXACTF)
   nodes, which can bundle many characters, which we have to compare
   separately. Occasionally, we also need access to extra regexp
   data. */
typedef struct
{
    regexp *origin;
    regnode *rn;
    int spent;
} Arrow;

#define GET_LITERAL(a) (((char *)((a)->rn + 1)) + (a)->spent)
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
  unsigned char bitmap[ANYOF_BITMAP_SIZE];
  unsigned char nbitmap[ANYOF_BITMAP_SIZE];
} ByteClass;

char *rc_error = 0;

unsigned char forced_byte[ANYOF_BITMAP_SIZE];

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
static unsigned char alphanumeric_classes[TYPE_COUNT];

/* true flags for NALNUM and its subsets, 0 otherwise */
static unsigned char non_alphanumeric_classes[TYPE_COUNT];

static unsigned char trivial_nodes[TYPE_COUNT];

static FCompare dispatch[TYPE_COUNT][TYPE_COUNT];

static int compare(int anchored, Arrow *a1, Arrow *a2);
static int compare_right_branch(int anchored, Arrow *a1, Arrow *a2);
static int compare_right_curly(int anchored, Arrow *a1, Arrow *a2);

static void init_bit_flag(BitFlag *bf, int c)
{
    assert(c >= 0);

    bf->offs = c / 8;
    bf->mask = 1 << (c % 8);
}

static void init_forced_byte()
{
    char forced_byte_expl[] = { 'a', 'b', 'c', 'e', 'f', 'x' };
    BitFlag bf;
    int i;

    memset(forced_byte, 0, sizeof(forced_byte));

    for (i = 0; i < sizeof(forced_byte_expl); ++i)
    {
	init_bit_flag(&bf, (unsigned char)forced_byte_expl[i]);
	forced_byte[bf.offs] |= bf.mask;
    }

    for (i = 0; i < 8; ++i)
    {
	init_bit_flag(&bf, (unsigned char)('0' + i));
	forced_byte[bf.offs] |= bf.mask;
    }
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

static char *get_regclass_desc(Arrow *a)
{
    regexp_internal *pr;
    U32 n;
    struct reg_data *rdata;

    assert(a->rn->type == ANYOF);
#ifndef RC_DEFAULT_UNICODE
    assert(a->rn->flags & ANYOF_LARGE);
#else
    assert(ANYOF_NONBITMAP(a->rn));
#endif

    /* basically copied from regexec.c:regclass_swash */
    n = ARG_LOC(a->rn);
    pr = RXi_GET(a->origin);
    if (!pr) /* this should have been tested by find_internal during
		initialization, but just in case... */
    {
	return 0;
    }

    rdata = pr->data;

    if ((n < rdata->count) &&
	(rdata->what[n] == 's')) {
        SV *rv = (SV *)(rdata->data[n]);
	AV *av = (AV *)SvRV(rv);
	SV **ary = AvARRAY(av);

	/* From regcomp.c:regclass: the 0th element stores the
	   character class description in its textual form. It isn't
	   very clear what exactly the textual form is, but we hope
	   it's 0-terminated. */
	return SvPV_nolen(*ary);
    }
      
    return 0;
}

static U16 get_regclass_map(char *desc, int invert)
{
    /* ignoring the difference between classes (i.e. IsAlnum &
       IsWord), which we probably shouldn't... */
    static char *names[] = { "IsSpacePerl", "IsAlnum", "IsWord",
			     "IsXPosixAlnum", "IsAlpha", "IsXPosixAlpha",
			     "IsDigit", "IsLower", "IsUpper" };
    static U16 blocks[] = { SPACE_BLOCK, ALNUM_BLOCK, ALNUM_BLOCK,
			    ALNUM_BLOCK, ALPHA_BLOCK, ALPHA_BLOCK,
			    NUMBER_BLOCK, LOWER_BLOCK, UPPER_BLOCK };

    static U16 superset[] = { NOT_SPACE_BLOCK,
			      NOT_ALNUM_BLOCK, NOT_ALNUM_BLOCK,
			      ALNUM_BLOCK, ALNUM_BLOCK,
			      ALPHA_BLOCK, ALPHA_BLOCK };
    static U16 subset[] = { ALNUM_BLOCK,
			    NOT_ALPHA_BLOCK, NOT_NUMBER_BLOCK,
			    ALPHA_BLOCK, NUMBER_BLOCK,
			    UPPER_BLOCK, LOWER_BLOCK };

    int i, j;
    U16 mask = 0;
    U16 prev_mask;

    char *p = strstr(desc, "utf8::");

    /* make sure *(p - 1) is valid */
    if (p == desc)
    {
	p = strstr(p + 6, "utf8::");
    }

    while (p)
    {
        char sign = *(p - 1);
	for (i = 0; i < SIZEOF_ARRAY(names); ++i)
	{
	    if (!strncmp(p + 6, names[i], strlen(names[i])))
	    {
		if (sign == '+')
		{
		    if (mask & (blocks[i] << MIRROR_SHIFT))
		    {
		        return invert ? 0 : EVERY_BLOCK;
		    }

		    mask |= blocks[i];
		}
		else if (sign == '!')
		{
		    if (mask & blocks[i])
		    {
		        return invert ? 0 : EVERY_BLOCK;
		    }

		    mask |= (blocks[i] << MIRROR_SHIFT);
		}
	    }
	}

	p = strstr(p + 6, "utf8::");
    }

    if ((mask & ALPHA_BLOCK) && (mask & NUMBER_BLOCK))
    {
	mask |= ALNUM_BLOCK;
    }

    if (invert)
    {
	mask = MIRROR_BLOCK(mask);
    }

    if ((mask & ALPHA_BLOCK) && (mask & NUMBER_BLOCK))
    {
	mask |= ALNUM_BLOCK;
    }

    /* extra cycle is inefficient but makes superset & subset
       definitions order-independent */
    prev_mask = 0;
    while (mask != prev_mask)
    {
        prev_mask = mask;
	for (i = 0; i < 2; ++i)
	{
	    for (j = 0; j < SIZEOF_ARRAY(superset); ++j)
	    {
		U16 b = superset[j];
		U16 s = subset[j];
		if (i)
		{
		    U16 t;

		    t = MIRROR_BLOCK(b);
		    b = MIRROR_BLOCK(s);
		    s = t;
		}

		if (mask & b)
		{
		    mask |= s;
		}
	    }
	}
    }

    return mask;
}

static U16 get_map(Arrow *a)
{
    U16 map = 0;

    /* fprintf(stderr, "enter get_map\n"); */
    assert(a->rn->type == ANYOF);

#ifndef RC_DEFAULT_UNICODE
    if (a->rn->flags & ANYOF_LARGE)
#else
    if (ANYOF_NONBITMAP(a->rn))
#endif
    {
	char *desc = get_regclass_desc(a);
	if (desc)
	{
	    /* fprintf(stderr, "desc = %s\n", desc); */
	    map = get_regclass_map(desc,
		!!(a->rn->flags & ANYOF_INVERT));
	    /* fprintf(stderr, "map = 0x%x\n", map); */
	}
    }

    return map;
}

static int get_assertion_offset(regnode *p)
{
    int offs;

    offs = ARG_LOC(p);
    if (offs <= 2)
    {
        rc_error = "Assertion offset too small";
	return -1;
    }

    return offs;
}

static int get_synth_offset(regnode *p)
{
    assert(!p->next_off);

    if (((p->type == EXACT) || (p->type == EXACTF)) &&
	(p->flags == 1))
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
        /* other flags obviously exist, but they haven't been seen yet
	   and it isn't clear what they mean */
        unsigned int unknown = p->flags & ~(ANYOF_INVERT |
	    ANYOF_LARGE | ANYOF_UNICODE | ANYOF_UNICODE_ALL);
        if (unknown)
	{
	    /* p[10] seems always 0 on Linux, but 0xfbfaf9f8 seen on
	       Windows; for '[\\w\\-_.]+\\.', both 0 and 0x20202020
	       observed in p[11] - wonder what those are... */
	    rc_error = "Unknown bitmap format";
	    return -1;
	}

	return (p->flags & ANYOF_LARGE) ? 12 : 11;
    }
    else if ((p->type == IFMATCH) || (p->type == UNLESSM))
    {
	return get_assertion_offset(p);
    }

    /* fprintf(stderr, "type %d\n", p->type); */
    rc_error = "Offset not set";
    return -1;
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

/* #define DEBUG_dump_data */

static regnode *find_internal(regexp *pt)
{
    regexp_internal *pr;
    regnode *p;
#ifdef DEBUG_dump_data
    struct reg_data *rdata;
    int n;
#endif

    assert(pt);

/* ActivePerl Build 1001 doesn't export PL_core_reg_engine, so
   the test, however useful, wouldn't link... */
#if !defined(ACTIVEPERL_PRODUCT)
    if (pt->engine && (pt->engine != &PL_core_reg_engine))
    {
        rc_error = "Alternative regexp engine not supported";
	return 0;
    }
#endif

    pr = RXi_GET(pt);
    if (!pr)
    {
        rc_error = "Internal regexp not set";
	return 0;
    }

    p = pr->program;
    if (!p)
    {
        rc_error = "Compiled regexp not set";
	return 0;
    }

    if (!((p->flags == REG_MAGIC) &&
	(p->next_off == 0)))
    {
        /* fprintf(stderr, "%d %d %d\n", p->flags, p->type, p->next_off); */
        rc_error = "Invalid regexp signature";
	return 0;
    }

#ifdef DEBUG_dump_data
    rdata = pr->data;
    if (rdata)
    {
        fprintf(stderr, "regexp data count = %d\n", (int)(rdata->count));
	for (n = 0; n < rdata->count; ++n)
	{
	    fprintf(stderr, "\twhat[%d] = %c\n", n, rdata->what[n]);
	}
    }
    else
    {
	fprintf(stderr, "no regexp data\n");
    }
#endif

    return p + 1;
}

static unsigned char parse_hex_digit(char d)
{
    unsigned char rv;

    d = tolower(d);

    if (('0' <= d) && (d <= '9'))
    {
        rv = d - '0';
    }
    else
    {
	rv = 10 + (d - 'a');
    }

    return rv;
}

static unsigned char parse_hex_byte(const char *first)
{
    return 16 * parse_hex_digit(*first) +
        parse_hex_digit(first[1]);
}

static unsigned get_forced_semantics(REGEXP *pt)
{
    const char *precomp = RX_PRECOMP(pt);
    U32 prelen = RX_PRELEN(pt);
    int quoted = 0;
    int matched;
    unsigned forced = 0;
    U32 i;
    BitFlag bf;
    char c;

    /* fprintf(stderr, "precomp = %*s\n", (int)prelen, precomp); */

    for (i = 0; i < prelen; ++i)
    {
	c = precomp[i];
	
	if (c == '.')
	{
	    /* a dot does match Unicode character - the problem is
	       that character might take up multiple bytes, and we
	       don't want to match just one of them... */
	    forced |= FORCED_BYTE;
	}
    
	if (!quoted)
	{
	    /* technically, the backslash might be in a comment, but
	       parsing that is too much hassle */
	    if (c == '\\')
	    {
		quoted = 1;
	    }
	}
	else
	{
	    matched = 0;

	    if (c == 'N')
	    {
	        /* we have special cases only for \r & \n... */
	        if ((i + 8 < prelen) &&
		    !memcmp(precomp + i + 1, "{U+00", 5) &&
		    isxdigit(precomp[i + 6]) && isxdigit(precomp[i + 7]) &&
		    (precomp[i + 8] == '}'))
		{
		    unsigned char x = parse_hex_byte(precomp + i + 6);
		    if ((x != '\r') && (x != '\n'))
		    {
			forced |= FORCED_CHAR;
		    }

		    i += 8;
		}
		else
		{
		    forced |= FORCED_CHAR;
		}

	        matched = 1;
	    }
	    else if (c == 'x')
	    {
	        if ((i + 2 < prelen) &&
		    isxdigit(precomp[i + 1]) && isxdigit(precomp[i + 2]))
		{
		    unsigned char x = parse_hex_byte(precomp + i + 1);
		    if ((x != '\r') && (x != '\n'))
		    {
			forced |= FORCED_BYTE;
		    }

		    matched = 1;
		    i += 2;
		}
	    }

	    /* ...and we aren't bothering to parse octal numbers
	       and \x{n+} at all... */

	    if (!matched)
	    {
		init_bit_flag(&bf, (unsigned char)c);
		if (forced_byte[bf.offs] & bf.mask)
		{
		    forced |= FORCED_BYTE;
		}
	    }

	    quoted = 0;
	}
    }

    return forced;
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

static regnode *alloc_terminated(regnode *p, int sz)
{
    regnode *alt;
    int last;

    /* fprintf(stderr, "enter alloc_terminated(, %d\n", sz); */

    assert(sz > 0);
    alt = alloc_alt(p, sz);
    if (!alt)
    {
	return 0;
    }

    last = alt[sz - 1].type;
    /* fprintf(stderr, "type: %d\n", last); */
    if ((last >= TYPE_COUNT) || !trivial_nodes[last])
    {
	rc_error = "Alternative doesn't end like subexpression";
	return 0;
    }

    alt[sz - 1].type = END;
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

    return q - p;
}

RCRegexp *rc_regcomp(SV *rs)
{
    RCRegexp *rx;

    if (!rs)
    {
	croak("No regexp to compare");
    }

    rx = pregcomp(rs, 0);
    if (!rx)
    {
	croak("Cannot compile regexp");
    }

    return rx;
}

void rc_regfree(RCRegexp *rx)
{
    if (rx)
    {
        pregfree(rx);
    }
}

static int compare_mismatch(int anchored, Arrow *a1, Arrow *a2)
{
    int rv;

    /* fprintf(stderr, "enter compare_mismatch(%d...)\n", anchored); */

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

    /* is it worth using StructCopy? */
    tail1 = *a1;
    rv = bump_with_check(&tail1);
    if (rv <= 0)
    {
        return rv;
    }

    tail2 = *a2;
    rv = bump_with_check(&tail2);
    if (rv <= 0)
    {
        return rv;
    }

    rv = compare(1, &tail1, &tail2);
    if (rv < 0)
    {
        return rv;
    }

    if (!rv)
    {
	rv = compare_mismatch(anchored, a1, a2);
    }
    else
    {
	*a1 = tail1;
	*a2 = tail2;
    }

    return rv;
}

static int compare_left_tail(int anchored, Arrow *a1, Arrow *a2)
{
    Arrow tail1;
    int rv;

    tail1 = *a1;
    rv = bump_with_check(&tail1);
    if (rv <= 0)
    {
        return rv;
    }

    return compare(anchored, &tail1, a2);
}

static int compare_after_assertion(int anchored, Arrow *a1, Arrow *a2)
{
    Arrow tail1;
    int offs;

    assert((a1->rn->type == IFMATCH) || (a1->rn->type == UNLESSM));

    offs = get_assertion_offset(a1->rn);
    if (offs < 0)
    {
	return offs;
    }

    tail1.origin = a1->origin;
    tail1.rn = a1->rn + offs;
    tail1.spent = 0;
    return compare(anchored, &tail1, a2);
}

static int compare_positive_assertions(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *alt1, *p2, *alt2;
    int rv, sz1, sz2;
    Arrow left, right;

    p1 = a1->rn;
    p2 = a2->rn;
    assert(p1->type == IFMATCH);
    assert(p2->type == IFMATCH);

    sz1 = get_assertion_offset(p1);
    if (sz1 < 0)
    {
	return -1;
    }

    sz2 = get_assertion_offset(p2);
    if (sz2 < 0)
    {
	return -1;
    }

    alt1 = alloc_terminated(p1 + 2, sz1 - 2);
    if (!alt1)
    {
	return -1;
    }

    alt2 = alloc_terminated(p2 + 2, sz2 - 2);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    left.origin = a1->origin;
    left.rn = alt1;
    left.spent = 0;
    right.origin = a2->origin;
    right.rn = alt2;
    right.spent = 0;
    rv = compare(0, &left, &right);

    free(alt1);
    free(alt2);

    if (rv <= 0)
    {
	return rv;
    }

    /* left & right.origin stays a1 & a2->origin, respectively */
    left.rn = p1 + sz1;
    left.spent = 0;
    right.rn = p2 + sz2;
    right.spent = 0;
    return compare(anchored, &left, &right);
}

static int compare_negative_assertions(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *alt1, *p2, *alt2;
    int rv, sz1, sz2;
    Arrow left, right;

    p1 = a1->rn;
    p2 = a2->rn;
    assert(p1->type == UNLESSM);
    assert(p2->type == UNLESSM);

    sz1 = get_assertion_offset(p1);
    if (sz1 < 0)
    {
	return -1;
    }

    sz2 = get_assertion_offset(p2);
    if (sz2 < 0)
    {
	return -1;
    }

    alt1 = alloc_terminated(p1 + 2, sz1 - 2);
    if (!alt1)
    {
	return -1;
    }

    alt2 = alloc_terminated(p2 + 2, sz2 - 2);
    if (!alt2)
    {
        free(alt1);
	return -1;
    }

    left.origin = a1->origin;
    left.rn = alt1;
    left.spent = 0;
    right.origin = a2->origin;
    right.rn = alt2;
    right.spent = 0;
    rv = compare(0, &right, &left);

    free(alt1);
    free(alt2);

    if (rv <= 0)
    {
	return rv;
    }

    /* left & right.origin stays a1 & a2->origin, respectively */
    left.rn = p1 + sz1;
    left.spent = 0;
    right.rn = p2 + sz2;
    right.spent = 0;
    return compare(anchored, &left, &right);
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

static unsigned char get_bitmap_byte(regnode *p, int i)
{
    unsigned char *bitmap;
    unsigned char loc;

    assert(p->type == ANYOF);

    bitmap = (unsigned char *)(p + 2);
    loc = bitmap[i];
    if (p->flags & ANYOF_INVERT)
    {
	loc = ~loc;
    }

    return loc;
}

static int compare_bitmaps(int anchored, Arrow *a1, Arrow *a2,
    unsigned char *b1, unsigned char *b2)
{
    unsigned char loc1, loc2;
    int i, sz;

    /* fprintf(stderr, "enter compare_bitmaps(%d, %d, %d)\n", anchored,
        a1->rn->type, a2->rn->type); */

#ifndef RC_DEFAULT_UNICODE
    sz = ANYOF_BITMAP_SIZE;
#else
    sz = (((a1->rn->flags & ANYOF_INVERT) &&
	    (a1->rn->flags & ANYOF_NON_UTF8_LATIN1_ALL)) ||
	(!(a2->rn->flags & ANYOF_INVERT) &&
	    (a2->rn->flags & ANYOF_NON_UTF8_LATIN1_ALL))) ? 16
        : ANYOF_BITMAP_SIZE;
#endif
    for (i = 0; i < sz; ++i)
    {
        loc1 = b1 ? b1[i] : get_bitmap_byte(a1->rn, i); 
        loc2 = b2 ? b2[i] : get_bitmap_byte(a2->rn, i); 
	if (loc1 & ~loc2)
	{
	    /* fprintf(stderr, "compare_bitmaps fails at %d: %d does not imply %d\n",
	        i, loc1, loc2); */
	    return compare_mismatch(anchored, a1, a2);
        }
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_anyof_multiline(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    Arrow tail1, tail2;
    unsigned char req;
    int i;

    /* fprintf(stderr, "enter compare_anyof_multiline\n"); */

    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == MBOL) || (a2->rn->type == MEOL));

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    init_bit_flag(&bf, '\n');
    for (i = 0; i < ANYOF_BITMAP_SIZE; ++i)
    {
        req = (i != bf.offs) ? 0 : bf.mask;
	if (get_bitmap_byte(a1->rn, i) != req)
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    tail1 = *a1;
    if (bump_regular(&tail1) <= 0)
    {
	return -1;
    }

    tail2 = *a2;
    if (bump_regular(&tail2) <= 0)
    {
	return -1;
    }

    return compare(1, &tail1, &tail2);
}

static int compare_anyof_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    int extra_left;

    /* fprintf(stderr, "enter compare_anyof_anyof(%d\n", anchored); */

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == ANYOF);

#ifndef RC_DEFAULT_UNICODE
    extra_left = a1->rn->flags & (ANYOF_UNICODE | ANYOF_LARGE);
#else
    extra_left = ANYOF_NONBITMAP(a1->rn);
#endif
    if ((extra_left || (a1->rn->flags & ANYOF_UNICODE_ALL)) &&
	!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	if (get_map(a1) & ~get_map(a2))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, 0, 0);
}

/* compare_bitmaps could replace this method, but when a class
   contains just a few characters, it seems more natural to compare
   them explicitly */
static int compare_short_byte_class(int anchored, Arrow *a1, Arrow *a2,
    ByteClass *left)
{
    BitFlag bf;
    int i;

    for (i = 0; i < left->expl_size; ++i)
    {
        init_bit_flag(&bf, (unsigned char)left->expl[i]);
	if (!(get_bitmap_byte(a2->rn, bf.offs) & bf.mask))
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

    /* fprintf(stderr, "flags = 0x%x\n", a2->rn->flags); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	if (!(get_map(a2) & ALNUM_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, alphanumeric.bitmap, 0);
}

static int compare_nalnum_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NALNUM);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	if (!(get_map(a2) & NOT_ALNUM_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, alphanumeric.nbitmap, 0);
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

    return compare_bitmaps(anchored, a1, a2, ndot.nbitmap, 0);
}

static int compare_nspace_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NSPACE);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, whitespace.nbitmap, 0);
}

static int compare_digit_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    /* fprintf(stderr, "enter compare_digit_anyof\n"); */

    assert(a1->rn->type == DIGIT);
    assert(a2->rn->type == ANYOF);

    /* fprintf(stderr, "right flags = %d\n", a2->rn->flags); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	if (!(get_map(a2) & NUMBER_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, digit.bitmap, 0);
}

static int compare_ndigit_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NDIGIT);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	if (!(get_map(a2) & NOT_NUMBER_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, digit.nbitmap, 0);
}

static int compare_exact_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    char *seq;

    /* fprintf(stderr, "enter compare_exact_anyof(%d, \n", anchored); */

    assert(a1->rn->type == EXACT);
    assert(a2->rn->type == ANYOF);

    seq = GET_LITERAL(a1);
    init_bit_flag(&bf, (unsigned char)(*seq));

    if (!(get_bitmap_byte(a2->rn, bf.offs) & bf.mask))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    char *seq;
    char unf[2];
    int i;

    /* fprintf(stderr, "enter compare_exactf_anyof(%d, \n", anchored); */

    assert(a1->rn->type == EXACTF);
    assert(a2->rn->type == ANYOF);

    seq = GET_LITERAL(a1);
    init_unfolded(unf, *seq);

    for (i = 0; i < 2; ++i)
    {
        init_bit_flag(&bf, (unsigned char)unf[i]);
	if (!(get_bitmap_byte(a2->rn, bf.offs) & bf.mask))
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

#if 0
    if (a1->rn->flags & ANYOF_UNICODE)
    {
	return compare_mismatch(anchored, a1, a2);
    }
#endif

    return compare_bitmaps(anchored, a1, a2, 0, ndot.nbitmap);
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

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, alphanumeric.bitmap);
}

static int compare_anyof_nalnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NALNUM);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, alphanumeric.nbitmap);
}

static int compare_anyof_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == SPACE);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, whitespace.bitmap);
}

static int compare_anyof_nspace(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NSPACE);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, whitespace.nbitmap);
}

static int compare_anyof_digit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == DIGIT);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, digit.bitmap);
}

static int compare_anyof_ndigit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NDIGIT);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, digit.nbitmap);
}

static int compare_anyof_exact(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    char *seq;
    int i;
    unsigned char req;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == EXACT);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    seq = GET_LITERAL(a2);
    init_bit_flag(&bf, *((unsigned char *)seq));

    for (i = 0; i < ANYOF_BITMAP_SIZE; ++i)
    {
        req = (i != bf.offs) ? 0 : bf.mask;
	if (get_bitmap_byte(a1->rn, i) != req)
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
    unsigned char right[ANYOF_BITMAP_SIZE];
    int i;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == EXACTF);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    seq = GET_LITERAL(a2);
    init_unfolded(unf, *seq);

    for (i = 0; i < 2; ++i)
    {
        init_bit_flag(bf + i, (unsigned char)(unf[i]));
    }

    if (bf[0].offs == bf[1].offs)
    {
	bf[0].mask = bf[1].mask = bf[0].mask | bf[1].mask;
    }

    memset(right, 0, ANYOF_BITMAP_SIZE);
    for (i = 0; i < 2; ++i)
    {
        right[bf[i].offs] = bf[i].mask;
    }

    return compare_bitmaps(anchored, a1, a2, 0, right);
}

static int compare_exact_exact(int anchored, Arrow *a1, Arrow *a2)
{
    char *q1, *q2;

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

    /* origins stay the same throughout the cycle */
    left.origin = a1->origin;
    right.origin = a2->origin;
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
    regnode *alt, *t1;
    Arrow left, right;
    int i, j, power, rv, sz, offs;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == BRANCH);

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

    left.origin = a1->origin;
    right.origin = a2->origin;
    right.rn = 0;

    for (i = 0; i < ANYOF_BITMAP_SIZE; ++i)
    {
        power = 1;
	for (j = 0; j < 8; ++j)
	{
	    if (get_bitmap_byte(a1->rn, i) & power)
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

    /* origins stay the same throughout the cycle */
    left.origin = a1->origin;
    right.origin = a2->origin;
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

    left.origin = a1->origin;
    left.rn = a1->rn;
    left.spent = a1->spent;

    offs = GET_OFFSET(p2);
    if (offs <= 0)
    {
	return -1;
    }

    right.origin = a2->origin;
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

	if (!anchored)
	{
	    rv = compare_right_star(1, a1, &right);
	}
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

static int compare_plus_plus(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;

    p1 = a1->rn;
    assert(p1->type == PLUS);
    p2 = a2->rn;
    assert(p2->type == PLUS);

    left.origin = a1->origin;
    left.rn = p1 + 1;
    left.spent = 0;

    right.origin = a2->origin;
    right.rn = p2 + 1;
    right.spent = 0;

    return compare(1, &left, &right);
}

static int compare_repeat_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;
    int rv, offs;

    p1 = a1->rn;
    assert((p1->type == PLUS) || (p1->type == STAR));
    p2 = a2->rn;
    assert(p2->type == STAR);
    /* fprintf(stderr, "enter compare_repeat_star(%d, %d, %d)\n",
       anchored, p1->type, p2->type); */

    left.origin = a1->origin;
    left.rn = p1 + 1;
    left.spent = 0;

    right.origin = a2->origin;
    right.rn = p2 + 1;
    right.spent = 0;

    rv = compare(1, &left, &right);
    /* fprintf(stderr, "inclusive compare returned %d\n", rv); */
    if (rv)
    {
	return rv;
    }

    offs = GET_OFFSET(p2);
    /* fprintf(stderr, "offs = %d\n", offs); */
    if (offs <= 0)
    {
	return -1;
    }

    right.origin = a2->origin;
    right.rn = p2 + offs;
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

    left.origin = a1->origin;
    left.rn = a1->rn;
    left.spent = a1->spent;

    offs = GET_OFFSET(p2);
    if (offs <= 0)
    {
	return -1;
    }

    right.origin = a2->origin;
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

	if ((cnt[1] > 0) && !anchored)
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
	    left.origin = a1->origin;
	    left.rn = q;
	    left.spent = 0;

	    end_offs = offs - 1;
	    orig_type = alt[end_offs].type;
	    alt[end_offs].type = END;

	    right.origin = a2->origin;
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

    left.origin = a1->origin;
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

    right.origin = a2->origin;
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

    cnt = (short *)(p1 + 1);
    if (cnt[0] < 0)
    {
	rc_error = "Left curly has negative minimum";
	return -1;
    }

    if (!cnt[0])
    {
        return compare_mismatch(anchored, a1, a2);
    }

    left.origin = a1->origin;
    left.rn = p1 + 2;
    left.spent = 0;

    right.origin = a2->origin;
    right.rn = p2 + 1;
    right.spent = 0;

    if (cnt[0] > 1)
    {
	anchored = 1;
    }

    return compare(anchored, &left, &right);
}

static int compare_curly_star(int anchored, Arrow *a1, Arrow *a2)
{
    regnode *p1, *p2;
    Arrow left, right;
    int rv;

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));
    p2 = a2->rn;
    assert(p2->type == STAR);

    left.origin = a1->origin;
    left.rn = p1 + 2;
    left.spent = 0;

    right.origin = a2->origin;
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

    left.origin = a1->origin;
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

    right.origin = a2->origin;
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

	left.origin = a1->origin;
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
	    left.origin = a1->origin;
	    left.rn = q;
	    left.spent = 0;

	    end_offs = offs - 1;
	    alt[end_offs].type = END;

	    right.origin = a2->origin;
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

    left.origin = a1->origin;
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

    /* fprintf(stderr, "enter compare_right_curly(%d...: a1->spent = %d, a2->spent = %d\n", anchored, a1->spent, a2->spent); */

    p2 = a2->rn;

    cnt = (short *)(p2 + 1);
    if (cnt[0] < 0)
    {
	rc_error = "Curly has negative minimum";
	return -1;
    }

    /* fprintf(stderr, "compare_right_curly: minimal repeat count = %d\n", cnt[0]); */

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

	right.origin = a2->origin;
	right.rn = p2 + 2;
	right.spent = 0;

	rv = compare(anchored, a1, &right);
	/* fprintf(stderr, "compare_right_curly: compare returned %d\n", rv); */
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

		right.origin = a2->origin;
		right.rn = alt;
		right.spent = 0;

		rv = compare(anchored, a1, &right);
		free(alt);
		return rv;
	    }

	    return 0;
	}

	if (cnt[0] == 1)
	{
	    return 1;
	}

	if (a1->rn->type == END)
	{
	    /* we presume the repeated argument matches something, which
	       isn't guaranteed, but it is conservative */
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
	    right.origin = a2->origin;
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
    int rv, offs;

    /* fprintf(stderr, "enter compare_curly_curly(%d...)\n", anchored); */

    p1 = a1->rn;
    assert((p1->type == CURLY) || (p1->type == CURLYM) ||
	   (p1->type == CURLYX));
    p2 = a2->rn;
    assert((p2->type == CURLY) || (p2->type == CURLYM) ||
	   (p2->type == CURLYX));

    cnt1 = (short *)(p1 + 1);
    /* fprintf(stderr, "*cnt1 = %d\n", cnt1[0]); */
    if (cnt1[0] < 0)
    {
	rc_error = "Negative minimum for left curly";
	return -1;
    }

    cnt2 = (short *)(p2 + 1);
    /* fprintf(stderr, "*cnt2 = %d\n", cnt2[0]); */
    if (cnt2[0] < 0)
    {
	rc_error = "Negative minimum for right curly";
	return -1;
    }

    if (cnt2[0] > cnt1[0]) /* FIXME: fails '(?:aa){1,}' => 'a{2,}' */
    {
        /* fprintf(stderr, "curly mismatch\n"); */
        return compare_mismatch(anchored, a1, a2);
    }

    left.origin = a1->origin;
    left.rn = p1 + 2;
    left.spent = 0;

    if (cnt1[1] > cnt2[1])
    {
	offs = get_jump_offset(p2);
        /* fprintf(stderr, "offs = %d\n", offs); */
	if (offs <= 0)
	{
	    return -1;
	}

	e2 = p2 + offs;
        /* fprintf(stderr, "e2->type = %d\n", e2->type); */
	if (e2->type != END)
	{
	    return compare_mismatch(anchored, a1, a2);	    
	}
    }

    right.origin = a2->origin;
    right.rn = p2 + 2;
    right.spent = 0;

    /* fprintf(stderr, "comparing tails\n"); */

    rv = compare(anchored, &left, &right);
    /* fprintf(stderr, "tail compare returned %d\n", rv); */
    return (!rv && !cnt2[0]) ? compare_next(anchored, a1, a2) : rv;
}

static int compare_bound(int anchored, Arrow *a1, Arrow *a2,
    int move_left, unsigned char *bitmap, char *lookup,
    unsigned char *oktypes)
{
    Arrow left, right;
    unsigned char t;
    int i;
    char *seq;

    assert((a2->rn->type == BOUND) || (a2->rn->type == NBOUND));

    left = *a1;

    if (bump_with_check(&left) <= 0)
    {
	return -1;
    }

    t = left.rn->type;
    if (t >= TYPE_COUNT)
    {
        rc_error = "Invalid node type";
        return -1;
    }
    else if (t == ANYOF)
    {
        /* fprintf(stderr, "next is bitmap; flags = 0x%x\n", left.rn->flags); */

        if (left.rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
	{
	    return compare_mismatch(anchored, a1, a2);
	}

	for (i = 0; i < ANYOF_BITMAP_SIZE; ++i)
	{
	    if (get_bitmap_byte(left.rn, i) & ~bitmap[i])
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

    right = *a2;
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
    unsigned char loc;
    FCompare cmp[2];
    int i;

    cmp[0] = compare_next_word;
    cmp[1] = compare_next_nword;
    for (i = 0; (i < ANYOF_BITMAP_SIZE) && (cmp[0] || cmp[1]); ++i)
    {
        loc = get_bitmap_byte(a1->rn, i);

        if (loc & ~bitmap[i])
	{
	     cmp[0] = 0;
	}

        if (loc & bitmap[i])
	{
	     cmp[1] = 0;
	}
    }

    if (cmp[0] && cmp[1])
    {
	rc_error = "Zero bitmap";
	return -1;
    }

    for (i = 0; i < SIZEOF_ARRAY(cmp); ++i)
    {
        if (cmp[i])
	{
	    return (cmp[i])(anchored, a1, a2);
	}
    }

    /* if would be more elegant to use compare_mismatch as a sentinel
       in cmp, but VC 2003 then warns that this function might be
       missing a return... */
    return compare_mismatch(anchored, a1, a2);
}

static int compare_anyof_bound(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == BOUND);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_anyof_bounds(anchored, a1, a2, alphanumeric.nbitmap);
}

static int compare_anyof_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NBOUND);

    if (a1->rn->flags & (ANYOF_UNICODE | ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

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

static int compare_open_open(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_tails(anchored, a1, a2);
}

static int compare_left_open(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_left_tail(anchored, a1, a2);
}

static int compare_right_open(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_next(anchored, a1, a2);
}

static int success(int anchored, Arrow *a1, Arrow *a2)
{
    return 1;
}

/* #define DEBUG_dump */

int rc_compare(RCRegexp *pt1, RCRegexp *pt2)
{
    Arrow a1, a2;
    regnode *p1, *p2;
#ifdef DEBUG_dump
    unsigned char *p;
    int i;    
#endif

#ifdef RC_FIST_CLASS_REGEXP
    a1.origin = SvANY(pt1);
    a2.origin = SvANY(pt2);
#else
    a1.origin = pt1;
    a2.origin = pt2;
#endif

    if ((get_forced_semantics(pt1) | get_forced_semantics(pt2)) == FORCED_MISMATCH)
    {
	return 0;
    }

    p1 = find_internal(a1.origin);
    if (!p1)
    {
	return -1;
    }

    p2 = find_internal(a2.origin);
    if (!p2)
    {
	return -1;
    }

#ifdef DEBUG_dump
    p = (unsigned char *)p1;
    for (i = 1; i <= 64; ++i)
    {
	fprintf(stderr, " %02x", (int)p[i - 1]);
	if (!(i % 4))
	{
	    fprintf(stderr, "\n");
	}
    }

    fprintf(stderr, "\n\n");

    p = (unsigned char *)p2;
    for (i = 1; i <= 64; ++i)
    {
	fprintf(stderr, " %02x", (int)p[i - 1]);
	if (!(i % 4))
	{
	    fprintf(stderr, "\n");
	}
    }

    fprintf(stderr, "\n\n");
#endif

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

    if ((a1->rn->type >= TYPE_COUNT) || (a2->rn->type >= TYPE_COUNT))
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

    /* could have used compile-time assertion, but why bother
       making it compatible... */
    assert(ANYOF_BITMAP_SIZE == 32);

    init_forced_byte();

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
        non_alphanumeric_classes[EOS] = non_alphanumeric_classes[EOL] = 
        non_alphanumeric_classes[SEOL] = 1;

    memset(trivial_nodes, 0, SIZEOF_ARRAY(trivial_nodes));
    trivial_nodes[SUCCEED] = trivial_nodes[NOTHING] =
        trivial_nodes[TAIL] = trivial_nodes[WHILEM] = 1;

    memset(dispatch, 0, sizeof(FCompare) * TYPE_COUNT * TYPE_COUNT);

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][END] = success;
    }

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][SUCCEED] = compare_next;
    }

    dispatch[SUCCEED][SUCCEED] = compare_tails;

    dispatch[SUCCEED][BOL] = compare_left_tail;
    dispatch[BOL][BOL] = compare_tails;
    dispatch[SBOL][BOL] = compare_tails;
    dispatch[BRANCH][BOL] = compare_left_branch;
    dispatch[NOTHING][BOL] = compare_left_tail;
    dispatch[TAIL][BOL] = compare_left_tail;
    dispatch[STAR][BOL] = compare_mismatch;
    dispatch[PLUS][BOL] = compare_left_plus;
    dispatch[CURLY][BOL] = compare_left_curly;
    dispatch[CURLYM][BOL] = compare_left_curly;
    dispatch[CURLYX][BOL] = compare_left_curly;
    dispatch[WHILEM][BOL] = compare_left_tail;
    dispatch[OPEN][BOL] = compare_left_open;
    dispatch[CLOSE][BOL] = compare_left_tail;
    dispatch[IFMATCH][BOL] = compare_after_assertion;
    dispatch[UNLESSM][BOL] = compare_after_assertion;
    dispatch[MINMOD][BOL] = compare_left_tail;
    dispatch[OPTIMIZED][BOL] = compare_left_tail;

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
    dispatch[TAIL][MBOL] = compare_left_tail;
    dispatch[STAR][MBOL] = compare_mismatch;
    dispatch[PLUS][MBOL] = compare_left_plus;
    dispatch[CURLY][MBOL] = compare_left_curly;
    dispatch[CURLYM][MBOL] = compare_left_curly;
    dispatch[CURLYX][MBOL] = compare_left_curly;
    dispatch[WHILEM][MBOL] = compare_left_tail;
    dispatch[OPEN][MBOL] = compare_left_open;
    dispatch[CLOSE][MBOL] = compare_left_tail;
    dispatch[IFMATCH][MBOL] = compare_after_assertion;
    dispatch[UNLESSM][MBOL] = compare_after_assertion;
    dispatch[MINMOD][MBOL] = compare_left_tail;
    dispatch[OPTIMIZED][MBOL] = compare_left_tail;

    dispatch[SUCCEED][SBOL] = compare_left_tail;
    dispatch[BOL][SBOL] = compare_tails;
    dispatch[SBOL][SBOL] = compare_tails;
    dispatch[BRANCH][SBOL] = compare_left_branch;
    dispatch[NOTHING][SBOL] = compare_left_tail;
    dispatch[TAIL][SBOL] = compare_left_tail;
    dispatch[STAR][SBOL] = compare_mismatch;
    dispatch[PLUS][SBOL] = compare_left_plus;
    dispatch[CURLY][SBOL] = compare_left_curly;
    dispatch[CURLYM][SBOL] = compare_left_curly;
    dispatch[CURLYX][SBOL] = compare_left_curly;
    dispatch[WHILEM][SBOL] = compare_left_tail;
    dispatch[OPEN][SBOL] = compare_left_open;
    dispatch[CLOSE][SBOL] = compare_left_tail;
    dispatch[IFMATCH][SBOL] = compare_after_assertion;
    dispatch[UNLESSM][SBOL] = compare_after_assertion;
    dispatch[MINMOD][SBOL] = compare_left_tail;
    dispatch[OPTIMIZED][SBOL] = compare_left_tail;

    dispatch[SUCCEED][EOS] = compare_left_tail;
    dispatch[EOS][EOS] = compare_tails;
    dispatch[EOL][EOS] = compare_mismatch;
    dispatch[SEOL][EOS] = compare_mismatch;
    dispatch[BRANCH][EOS] = compare_left_branch;
    dispatch[NOTHING][EOS] = compare_left_tail;
    dispatch[TAIL][EOS] = compare_left_tail;
    dispatch[STAR][EOS] = compare_mismatch;
    dispatch[PLUS][EOS] = compare_left_plus;
    dispatch[CURLY][EOS] = compare_left_curly;
    dispatch[CURLYM][EOS] = compare_left_curly;
    dispatch[CURLYX][EOS] = compare_left_curly;
    dispatch[WHILEM][EOS] = compare_left_tail;
    dispatch[OPEN][EOS] = compare_left_open;
    dispatch[CLOSE][EOS] = compare_left_tail;
    dispatch[IFMATCH][EOS] = compare_after_assertion;
    dispatch[UNLESSM][EOS] = compare_after_assertion;
    dispatch[MINMOD][EOS] = compare_left_tail;
    dispatch[OPTIMIZED][EOS] = compare_left_tail;

    dispatch[SUCCEED][EOL] = compare_left_tail;
    dispatch[EOS][EOL] = compare_tails;
    dispatch[EOL][EOL] = compare_tails;
    dispatch[SEOL][EOL] = compare_tails;
    dispatch[BRANCH][EOL] = compare_left_branch;
    dispatch[NOTHING][EOL] = compare_left_tail;
    dispatch[TAIL][EOL] = compare_left_tail;
    dispatch[STAR][EOL] = compare_mismatch;
    dispatch[PLUS][EOL] = compare_left_plus;
    dispatch[CURLY][EOL] = compare_left_curly;
    dispatch[CURLYM][EOL] = compare_left_curly;
    dispatch[CURLYX][EOL] = compare_left_curly;
    dispatch[WHILEM][EOL] = compare_left_tail;
    dispatch[OPEN][EOL] = compare_left_open;
    dispatch[CLOSE][EOL] = compare_left_tail;
    dispatch[IFMATCH][EOL] = compare_after_assertion;
    dispatch[UNLESSM][EOL] = compare_after_assertion;
    dispatch[MINMOD][EOL] = compare_left_tail;
    dispatch[OPTIMIZED][EOL] = compare_left_tail;

    dispatch[SUCCEED][MEOL] = compare_left_tail;
    dispatch[EOS][MEOL] = compare_tails;
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
    dispatch[TAIL][MEOL] = compare_left_tail;
    dispatch[STAR][MEOL] = compare_mismatch;
    dispatch[PLUS][MEOL] = compare_left_plus;
    dispatch[CURLY][MEOL] = compare_left_curly;
    dispatch[CURLYM][MEOL] = compare_left_curly;
    dispatch[CURLYX][MEOL] = compare_left_curly;
    dispatch[WHILEM][MEOL] = compare_left_tail;
    dispatch[OPEN][MEOL] = compare_left_open;
    dispatch[CLOSE][MEOL] = compare_left_tail;
    dispatch[IFMATCH][MEOL] = compare_after_assertion;
    dispatch[UNLESSM][MEOL] = compare_after_assertion;
    dispatch[MINMOD][MEOL] = compare_left_tail;
    dispatch[OPTIMIZED][MEOL] = compare_left_tail;

    dispatch[SUCCEED][SEOL] = compare_left_tail;
    dispatch[EOS][SEOL] = compare_tails;
    dispatch[EOL][SEOL] = compare_tails;
    dispatch[SEOL][SEOL] = compare_tails;
    dispatch[BRANCH][SEOL] = compare_left_branch;
    dispatch[NOTHING][SEOL] = compare_left_tail;
    dispatch[TAIL][SEOL] = compare_left_tail;
    dispatch[STAR][SEOL] = 0;
    dispatch[PLUS][SEOL] = compare_left_plus;
    dispatch[CURLY][SEOL] = compare_left_curly;
    dispatch[CURLYM][SEOL] = compare_left_curly;
    dispatch[CURLYX][SEOL] = compare_left_curly;
    dispatch[WHILEM][SEOL] = compare_left_tail;
    dispatch[OPEN][SEOL] = compare_left_open;
    dispatch[CLOSE][SEOL] = compare_left_tail;
    dispatch[IFMATCH][SEOL] = compare_after_assertion;
    dispatch[UNLESSM][SEOL] = compare_after_assertion;
    dispatch[MINMOD][SEOL] = compare_left_tail;
    dispatch[OPTIMIZED][SEOL] = compare_left_tail;

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
    dispatch[TAIL][BOUND] = compare_left_tail;
    dispatch[CURLY][BOUND] = compare_left_curly;
    dispatch[CURLYM][BOUND] = compare_left_curly;
    dispatch[CURLYX][BOUND] = compare_left_curly;
    dispatch[WHILEM][BOUND] = compare_left_tail;
    dispatch[OPEN][BOUND] = compare_left_open;
    dispatch[CLOSE][BOUND] = compare_left_tail;
    dispatch[IFMATCH][BOUND] = compare_after_assertion;
    dispatch[UNLESSM][BOUND] = compare_after_assertion;
    dispatch[MINMOD][BOUND] = compare_left_tail;
    dispatch[OPTIMIZED][BOUND] = compare_left_tail;

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
    dispatch[TAIL][NBOUND] = compare_left_tail;
    dispatch[CURLY][NBOUND] = compare_left_curly;
    dispatch[CURLYM][NBOUND] = compare_left_curly;
    dispatch[CURLYX][NBOUND] = compare_left_curly;
    dispatch[WHILEM][NBOUND] = compare_left_tail;
    dispatch[OPEN][NBOUND] = compare_left_open;
    dispatch[CLOSE][NBOUND] = compare_left_tail;
    dispatch[IFMATCH][NBOUND] = compare_after_assertion;
    dispatch[UNLESSM][NBOUND] = compare_after_assertion;
    dispatch[MINMOD][NBOUND] = compare_left_tail;
    dispatch[OPTIMIZED][NBOUND] = compare_left_tail;

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
    dispatch[TAIL][REG_ANY] = compare_left_tail;
    dispatch[STAR][REG_ANY] = compare_mismatch;
    dispatch[PLUS][REG_ANY] = compare_left_plus;
    dispatch[CURLY][REG_ANY] = compare_left_curly;
    dispatch[CURLYM][REG_ANY] = compare_left_curly;
    dispatch[CURLYX][REG_ANY] = compare_left_curly;
    dispatch[WHILEM][REG_ANY] = compare_left_tail;
    dispatch[OPEN][REG_ANY] = compare_left_open;
    dispatch[CLOSE][REG_ANY] = compare_left_tail;
    dispatch[IFMATCH][REG_ANY] = compare_after_assertion;
    dispatch[UNLESSM][REG_ANY] = compare_after_assertion;
    dispatch[MINMOD][REG_ANY] = compare_left_tail;
    dispatch[OPTIMIZED][REG_ANY] = compare_left_tail;

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
    dispatch[TAIL][SANY] = compare_left_tail;
    dispatch[STAR][SANY] = compare_mismatch;
    dispatch[PLUS][SANY] = compare_left_plus;
    dispatch[CURLY][SANY] = compare_left_curly;
    dispatch[CURLYM][SANY] = compare_left_curly;
    dispatch[CURLYX][SANY] = compare_left_curly;
    dispatch[WHILEM][SANY] = compare_left_tail;
    dispatch[OPEN][SANY] = compare_left_open;
    dispatch[CLOSE][SANY] = compare_left_tail;
    dispatch[IFMATCH][SANY] = compare_after_assertion;
    dispatch[UNLESSM][SANY] = compare_after_assertion;
    dispatch[MINMOD][SANY] = compare_left_tail;
    dispatch[OPTIMIZED][SANY] = compare_left_tail;

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
    dispatch[TAIL][ANYOF] = compare_left_tail;
    dispatch[STAR][ANYOF] = compare_mismatch;
    dispatch[PLUS][ANYOF] = compare_left_plus;
    dispatch[CURLY][ANYOF] = compare_left_curly;
    dispatch[CURLYM][ANYOF] = compare_left_curly;
    dispatch[CURLYX][ANYOF] = compare_left_curly;
    dispatch[WHILEM][ANYOF] = compare_left_tail;
    dispatch[OPEN][ANYOF] = compare_left_open;
    dispatch[CLOSE][ANYOF] = compare_left_tail;
    dispatch[IFMATCH][ANYOF] = compare_after_assertion;
    dispatch[UNLESSM][ANYOF] = compare_after_assertion;
    dispatch[MINMOD][ANYOF] = compare_left_tail;
    dispatch[OPTIMIZED][ANYOF] = compare_left_tail;

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
    dispatch[TAIL][ALNUM] = compare_left_tail;
    dispatch[STAR][ALNUM] = compare_mismatch;
    dispatch[PLUS][ALNUM] = compare_left_plus;
    dispatch[CURLY][ALNUM] = compare_left_curly;
    dispatch[CURLYM][ALNUM] = compare_left_curly;
    dispatch[CURLYX][ALNUM] = compare_left_curly;
    dispatch[WHILEM][ALNUM] = compare_left_tail;
    dispatch[OPEN][ALNUM] = compare_left_open;
    dispatch[CLOSE][ALNUM] = compare_left_tail;
    dispatch[IFMATCH][ALNUM] = compare_after_assertion;
    dispatch[UNLESSM][ALNUM] = compare_after_assertion;
    dispatch[MINMOD][ALNUM] = compare_left_tail;
    dispatch[OPTIMIZED][ALNUM] = compare_left_tail;

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
    dispatch[TAIL][NALNUM] = compare_left_tail;
    dispatch[STAR][NALNUM] = compare_mismatch;
    dispatch[PLUS][NALNUM] = compare_left_plus;
    dispatch[CURLY][NALNUM] = compare_left_curly;
    dispatch[CURLYM][NALNUM] = compare_left_curly;
    dispatch[CURLYX][NALNUM] = compare_left_curly;
    dispatch[WHILEM][NALNUM] = compare_left_tail;
    dispatch[OPEN][NALNUM] = compare_left_open;
    dispatch[CLOSE][NALNUM] = compare_left_tail;
    dispatch[IFMATCH][NALNUM] = compare_after_assertion;
    dispatch[UNLESSM][NALNUM] = compare_after_assertion;
    dispatch[MINMOD][NALNUM] = compare_left_tail;
    dispatch[OPTIMIZED][NALNUM] = compare_left_tail;

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
    dispatch[TAIL][SPACE] = compare_left_tail;
    dispatch[STAR][SPACE] = compare_mismatch;
    dispatch[PLUS][SPACE] = compare_left_plus;
    dispatch[CURLY][SPACE] = compare_left_curly;
    dispatch[CURLYM][SPACE] = compare_left_curly;
    dispatch[CURLYX][SPACE] = compare_left_curly;
    dispatch[WHILEM][SPACE] = compare_left_tail;
    dispatch[OPEN][SPACE] = compare_left_open;
    dispatch[CLOSE][SPACE] = compare_left_tail;
    dispatch[IFMATCH][SPACE] = compare_after_assertion;
    dispatch[UNLESSM][SPACE] = compare_after_assertion;
    dispatch[MINMOD][SPACE] = compare_left_tail;
    dispatch[OPTIMIZED][SPACE] = compare_left_tail;

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
    dispatch[TAIL][NSPACE] = compare_left_tail;
    dispatch[STAR][NSPACE] = compare_mismatch;
    dispatch[PLUS][NSPACE] = compare_left_plus;
    dispatch[CURLY][NSPACE] = compare_left_curly;
    dispatch[CURLYM][NSPACE] = compare_left_curly;
    dispatch[CURLYX][NSPACE] = compare_left_curly;
    dispatch[WHILEM][NSPACE] = compare_left_tail;
    dispatch[OPEN][NSPACE] = compare_left_open;
    dispatch[CLOSE][NSPACE] = compare_left_tail;
    dispatch[IFMATCH][NSPACE] = compare_after_assertion;
    dispatch[UNLESSM][NSPACE] = compare_after_assertion;
    dispatch[MINMOD][NSPACE] = compare_left_tail;
    dispatch[OPTIMIZED][NSPACE] = compare_left_tail;

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
    dispatch[TAIL][DIGIT] = compare_left_tail;
    dispatch[STAR][DIGIT] = compare_mismatch;
    dispatch[PLUS][DIGIT] = compare_left_plus;
    dispatch[CURLY][DIGIT] = compare_left_curly;
    dispatch[CURLYM][DIGIT] = compare_left_curly;
    dispatch[CURLYX][DIGIT] = compare_left_curly;
    dispatch[WHILEM][DIGIT] = compare_left_tail;
    dispatch[OPEN][DIGIT] = compare_left_open;
    dispatch[CLOSE][DIGIT] = compare_left_tail;
    dispatch[IFMATCH][DIGIT] = compare_after_assertion;
    dispatch[UNLESSM][DIGIT] = compare_after_assertion;
    dispatch[MINMOD][DIGIT] = compare_left_tail;
    dispatch[OPTIMIZED][DIGIT] = compare_left_tail;

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
    dispatch[TAIL][NDIGIT] = compare_left_tail;
    dispatch[STAR][NDIGIT] = compare_mismatch;
    dispatch[PLUS][NDIGIT] = compare_left_plus;
    dispatch[CURLY][NDIGIT] = compare_left_curly;
    dispatch[CURLYM][NDIGIT] = compare_left_curly;
    dispatch[CURLYX][NDIGIT] = compare_left_curly;
    dispatch[WHILEM][NDIGIT] = compare_left_tail;
    dispatch[OPEN][NDIGIT] = compare_left_open;
    dispatch[CLOSE][NDIGIT] = compare_left_tail;
    dispatch[IFMATCH][NDIGIT] = compare_after_assertion;
    dispatch[UNLESSM][NDIGIT] = compare_after_assertion;
    dispatch[MINMOD][NDIGIT] = compare_left_tail;
    dispatch[OPTIMIZED][NDIGIT] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][BRANCH] = compare_right_branch;
    }

    dispatch[SUCCEED][BRANCH] = compare_left_tail;
    dispatch[ANYOF][BRANCH] = compare_anyof_branch;
    dispatch[BRANCH][BRANCH] = compare_left_branch;
    dispatch[NOTHING][BRANCH] = compare_left_tail;
    dispatch[TAIL][BRANCH] = compare_left_tail;
    dispatch[WHILEM][BRANCH] = compare_left_tail;
    dispatch[OPEN][BRANCH] = compare_left_open;
    dispatch[CLOSE][BRANCH] = compare_left_tail;
    dispatch[IFMATCH][BRANCH] = compare_after_assertion;
    dispatch[UNLESSM][BRANCH] = compare_after_assertion;
    dispatch[MINMOD][BRANCH] = compare_left_tail;
    dispatch[OPTIMIZED][BRANCH] = compare_left_tail;

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
    dispatch[TAIL][EXACT] = compare_left_tail;
    dispatch[STAR][EXACT] = compare_mismatch;
    dispatch[PLUS][EXACT] = compare_left_plus;
    dispatch[CURLY][EXACT] = compare_left_curly;
    dispatch[CURLYM][EXACT] = compare_left_curly;
    dispatch[CURLYX][EXACT] = compare_left_curly;
    dispatch[WHILEM][EXACT] = compare_left_tail;
    dispatch[OPEN][EXACT] = compare_left_open;
    dispatch[CLOSE][EXACT] = compare_left_tail;
    dispatch[IFMATCH][EXACT] = compare_after_assertion;
    dispatch[UNLESSM][EXACT] = compare_after_assertion;
    dispatch[MINMOD][EXACT] = compare_left_tail;
    dispatch[OPTIMIZED][EXACT] = compare_left_tail;

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
    dispatch[TAIL][EXACTF] = compare_left_tail;
    dispatch[STAR][EXACTF] = compare_mismatch;
    dispatch[PLUS][EXACTF] = compare_left_plus;
    dispatch[CURLY][EXACTF] = compare_left_curly;
    dispatch[CURLYM][EXACTF] = compare_left_curly;
    dispatch[CURLYX][EXACTF] = compare_left_curly;
    dispatch[WHILEM][EXACTF] = compare_left_tail;
    dispatch[OPEN][EXACTF] = compare_left_open;
    dispatch[CLOSE][EXACTF] = compare_left_tail;
    dispatch[IFMATCH][EXACTF] = compare_after_assertion;
    dispatch[UNLESSM][EXACTF] = compare_after_assertion;
    dispatch[MINMOD][EXACTF] = compare_left_tail;
    dispatch[OPTIMIZED][EXACTF] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
        dispatch[i][NOTHING] = compare_next;
    }

    dispatch[SUCCEED][NOTHING] = compare_tails;
    dispatch[NOTHING][NOTHING] = compare_tails;
    dispatch[TAIL][NOTHING] = compare_tails;
    dispatch[WHILEM][NOTHING] = compare_tails;
    dispatch[CLOSE][NOTHING] = compare_tails;
    dispatch[MINMOD][NOTHING] = compare_tails;
    dispatch[OPTIMIZED][NOTHING] = compare_tails;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
        dispatch[i][TAIL] = compare_next;
    }

    dispatch[SUCCEED][TAIL] = compare_tails;
    dispatch[NOTHING][TAIL] = compare_tails;
    dispatch[TAIL][TAIL] = compare_tails;
    dispatch[WHILEM][TAIL] = compare_tails;
    dispatch[CLOSE][TAIL] = compare_tails;
    dispatch[MINMOD][TAIL] = compare_tails;
    dispatch[OPTIMIZED][TAIL] = compare_tails;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][STAR] = compare_right_star;
    }

    dispatch[SUCCEED][STAR] = compare_left_tail;
    dispatch[EOS][STAR] = compare_tails;
    dispatch[EOL][STAR] = compare_tails;
    dispatch[MEOL][STAR] = compare_tails;
    dispatch[SEOL][STAR] = compare_tails;
    dispatch[NOTHING][STAR] = compare_left_tail;
    dispatch[TAIL][STAR] = compare_left_tail;
    dispatch[STAR][STAR] = compare_repeat_star;
    dispatch[PLUS][STAR] = compare_repeat_star;
    dispatch[CURLY][STAR] = compare_curly_star;
    dispatch[CURLYM][STAR] = compare_curly_star;
    dispatch[CURLYX][STAR] = compare_curly_star;
    dispatch[WHILEM][STAR] = compare_left_tail;
    dispatch[OPEN][STAR] = compare_left_open;
    dispatch[CLOSE][STAR] = compare_left_tail;
    dispatch[IFMATCH][STAR] = compare_after_assertion;
    dispatch[UNLESSM][STAR] = compare_after_assertion;
    dispatch[MINMOD][STAR] = compare_left_tail;
    dispatch[OPTIMIZED][STAR] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][PLUS] = compare_right_plus;
    }

    dispatch[SUCCEED][PLUS] = compare_left_tail;
    dispatch[NOTHING][PLUS] = compare_left_tail;
    dispatch[TAIL][PLUS] = compare_left_tail;
    dispatch[PLUS][PLUS] = compare_plus_plus;
    dispatch[CURLY][PLUS] = compare_curly_plus;
    dispatch[CURLYM][PLUS] = compare_curly_plus;
    dispatch[CURLYX][PLUS] = compare_curly_plus;
    dispatch[WHILEM][PLUS] = compare_left_tail;
    dispatch[OPEN][PLUS] = compare_left_open;
    dispatch[CLOSE][PLUS] = compare_left_tail;
    dispatch[IFMATCH][PLUS] = compare_after_assertion;
    dispatch[UNLESSM][PLUS] = compare_after_assertion;
    dispatch[MINMOD][PLUS] = compare_left_tail;
    dispatch[OPTIMIZED][PLUS] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][CURLY] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLY] = compare_left_tail;
    dispatch[NOTHING][CURLY] = compare_left_tail;
    dispatch[TAIL][CURLY] = compare_left_tail;
    dispatch[PLUS][CURLY] = compare_plus_curly;
    dispatch[CURLY][CURLY] = compare_curly_curly;
    dispatch[CURLYM][CURLY] = compare_curly_curly;
    dispatch[CURLYX][CURLY] = compare_curly_curly;
    dispatch[WHILEM][CURLY] = compare_left_tail;
    dispatch[OPEN][CURLY] = compare_left_open;
    dispatch[CLOSE][CURLY] = compare_left_tail;
    dispatch[IFMATCH][CURLY] = compare_after_assertion;
    dispatch[UNLESSM][CURLY] = compare_after_assertion;
    dispatch[MINMOD][CURLY] = compare_left_tail;
    dispatch[OPTIMIZED][CURLY] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][CURLYM] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLYM] = compare_left_tail;
    dispatch[NOTHING][CURLYM] = compare_left_tail;
    dispatch[TAIL][CURLYM] = compare_left_tail;
    dispatch[PLUS][CURLYM] = compare_plus_curly;
    dispatch[CURLY][CURLYM] = compare_curly_curly;
    dispatch[CURLYM][CURLYM] = compare_curly_curly;
    dispatch[CURLYX][CURLYM] = compare_curly_curly;
    dispatch[WHILEM][CURLYM] = compare_left_tail;
    dispatch[OPEN][CURLYM] = compare_left_open;
    dispatch[CLOSE][CURLYM] = compare_left_tail;
    dispatch[IFMATCH][CURLYM] = compare_after_assertion;
    dispatch[UNLESSM][CURLYM] = compare_after_assertion;
    dispatch[MINMOD][CURLYM] = compare_left_tail;
    dispatch[OPTIMIZED][CURLYM] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][CURLYX] = compare_right_curly;
    }

    dispatch[SUCCEED][CURLYX] = compare_left_tail;
    dispatch[NOTHING][CURLYX] = compare_left_tail;
    dispatch[TAIL][CURLYX] = compare_left_tail;
    dispatch[PLUS][CURLYX] = compare_plus_curly;
    dispatch[CURLY][CURLYX] = compare_curly_curly;
    dispatch[CURLYM][CURLYX] = compare_curly_curly;
    dispatch[CURLYX][CURLYX] = compare_curly_curly;
    dispatch[WHILEM][CURLYX] = compare_left_tail;
    dispatch[OPEN][CURLYX] = compare_left_open;
    dispatch[CLOSE][CURLYX] = compare_left_tail;
    dispatch[IFMATCH][CURLYX] = compare_after_assertion;
    dispatch[UNLESSM][CURLYX] = compare_after_assertion;
    dispatch[MINMOD][CURLYX] = compare_left_tail;
    dispatch[OPTIMIZED][CURLYX] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][WHILEM] = compare_next;
    }

    dispatch[SUCCEED][WHILEM] = compare_tails;
    dispatch[NOTHING][WHILEM] = compare_tails;
    dispatch[TAIL][WHILEM] = compare_tails;
    dispatch[WHILEM][WHILEM] = compare_tails;
    dispatch[CLOSE][WHILEM] = compare_tails;
    dispatch[MINMOD][WHILEM] = compare_tails;
    dispatch[OPTIMIZED][WHILEM] = compare_tails;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][OPEN] = compare_right_open;
    }

    dispatch[OPEN][OPEN] = compare_open_open;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][CLOSE] = compare_next;
    }

    dispatch[SUCCEED][CLOSE] = compare_tails;
    dispatch[NOTHING][CLOSE] = compare_tails;
    dispatch[TAIL][CLOSE] = compare_tails;
    dispatch[WHILEM][CLOSE] = compare_tails;
    dispatch[CLOSE][CLOSE] = compare_tails;
    dispatch[MINMOD][CLOSE] = compare_tails;
    dispatch[OPTIMIZED][CLOSE] = compare_tails;

    dispatch[SUCCEED][IFMATCH] = compare_left_tail;
    dispatch[BOL][IFMATCH] = compare_bol;
    dispatch[MBOL][IFMATCH] = compare_bol;
    dispatch[SBOL][IFMATCH] = compare_bol;
    dispatch[BOUND][IFMATCH] = compare_mismatch;
    dispatch[NBOUND][IFMATCH] = compare_mismatch;
    dispatch[REG_ANY][IFMATCH] = compare_mismatch;
    dispatch[SANY][IFMATCH] = compare_mismatch;
    dispatch[ANYOF][IFMATCH] = compare_mismatch;
    dispatch[ALNUM][IFMATCH] = compare_mismatch;
    dispatch[NALNUM][IFMATCH] = compare_mismatch;
    dispatch[SPACE][IFMATCH] = compare_mismatch;
    dispatch[NSPACE][IFMATCH] = compare_mismatch;
    dispatch[DIGIT][IFMATCH] = compare_mismatch;
    dispatch[NDIGIT][IFMATCH] = compare_mismatch;
    dispatch[BRANCH][IFMATCH] = compare_mismatch;
    dispatch[EXACT][IFMATCH] = compare_mismatch;
    dispatch[EXACTF][IFMATCH] = compare_mismatch;
    dispatch[NOTHING][IFMATCH] = compare_left_tail;
    dispatch[TAIL][IFMATCH] = compare_left_tail;
    dispatch[STAR][IFMATCH] = compare_mismatch;
    dispatch[PLUS][IFMATCH] = compare_mismatch;
    dispatch[CURLY][IFMATCH] = compare_mismatch;
    dispatch[CURLYM][IFMATCH] = compare_mismatch;
    dispatch[CURLYX][IFMATCH] = compare_mismatch;
    dispatch[WHILEM][IFMATCH] = compare_left_tail;
    dispatch[OPEN][IFMATCH] = compare_left_open;
    dispatch[CLOSE][IFMATCH] = compare_left_tail;
    dispatch[IFMATCH][IFMATCH] = compare_positive_assertions;
    dispatch[UNLESSM][IFMATCH] = compare_mismatch;
    dispatch[MINMOD][IFMATCH] = compare_left_tail;
    dispatch[OPTIMIZED][IFMATCH] = compare_left_tail;

    dispatch[SUCCEED][UNLESSM] = compare_left_tail;
    dispatch[BOL][UNLESSM] = compare_bol;
    dispatch[MBOL][UNLESSM] = compare_bol;
    dispatch[SBOL][UNLESSM] = compare_bol;
    dispatch[BOUND][UNLESSM] = compare_mismatch;
    dispatch[NBOUND][UNLESSM] = compare_mismatch;
    dispatch[REG_ANY][UNLESSM] = compare_mismatch;
    dispatch[SANY][UNLESSM] = compare_mismatch;
    dispatch[ANYOF][UNLESSM] = compare_mismatch;
    dispatch[ALNUM][UNLESSM] = compare_mismatch;
    dispatch[NALNUM][UNLESSM] = compare_mismatch;
    dispatch[SPACE][UNLESSM] = compare_mismatch;
    dispatch[NSPACE][UNLESSM] = compare_mismatch;
    dispatch[DIGIT][UNLESSM] = compare_mismatch;
    dispatch[NDIGIT][UNLESSM] = compare_mismatch;
    dispatch[BRANCH][UNLESSM] = compare_mismatch;
    dispatch[EXACT][UNLESSM] = compare_mismatch;
    dispatch[EXACTF][UNLESSM] = compare_mismatch;
    dispatch[NOTHING][UNLESSM] = compare_left_tail;
    dispatch[TAIL][UNLESSM] = compare_left_tail;
    dispatch[STAR][UNLESSM] = compare_mismatch;
    dispatch[PLUS][UNLESSM] = compare_mismatch;
    dispatch[CURLY][UNLESSM] = compare_mismatch;
    dispatch[CURLYM][UNLESSM] = compare_mismatch;
    dispatch[CURLYX][UNLESSM] = compare_mismatch;
    dispatch[WHILEM][UNLESSM] = compare_left_tail;
    dispatch[OPEN][UNLESSM] = compare_left_open;
    dispatch[CLOSE][UNLESSM] = compare_left_tail;
    dispatch[IFMATCH][UNLESSM] = compare_mismatch;
    dispatch[UNLESSM][UNLESSM] = compare_negative_assertions;
    dispatch[MINMOD][UNLESSM] = compare_left_tail;
    dispatch[OPTIMIZED][UNLESSM] = compare_left_tail;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][MINMOD] = compare_next;
    }

    dispatch[SUCCEED][MINMOD] = compare_tails;
    dispatch[NOTHING][MINMOD] = compare_tails;
    dispatch[TAIL][MINMOD] = compare_tails;
    dispatch[WHILEM][MINMOD] = compare_tails;
    dispatch[CLOSE][MINMOD] = compare_tails;
    dispatch[MINMOD][MINMOD] = compare_tails;
    dispatch[OPTIMIZED][MINMOD] = compare_tails;

    for (i = 0; i < TYPE_COUNT; ++i)
    {
	dispatch[i][OPTIMIZED] = compare_next;
    }

    dispatch[SUCCEED][OPTIMIZED] = compare_tails;
    dispatch[NOTHING][OPTIMIZED] = compare_tails;
    dispatch[TAIL][OPTIMIZED] = compare_tails;
    dispatch[WHILEM][OPTIMIZED] = compare_tails;
    dispatch[CLOSE][OPTIMIZED] = compare_tails;
    dispatch[MINMOD][OPTIMIZED] = compare_tails;
    dispatch[OPTIMIZED][OPTIMIZED] = compare_tails;
}
