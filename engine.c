#include "engine.h"
#include "regnodes.h"
#include "regcomp.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

#if PERL_API_REVISION != 5
#error This module is only for Perl 5
#else
#if PERL_API_VERSION == 16
#define RC_ANYOF_UTF8 0
#else
#if PERL_API_VERSION == 18
#define RC_POSIX_NODES

#define RC_ANYOF_UTF8 0
#else
#if PERL_API_VERSION == 20
#define RC_POSIX_NODES
#define RC_INVLIST_EX

#define RC_ANYOF_UTF8 ANYOF_UTF8

/* renamed */
#define ANYOF_NON_UTF8_LATIN1_ALL ANYOF_NON_UTF8_NON_ASCII_ALL

/* no longer exists - using 5.18 definition */
#define ANYOF_NONBITMAP(node)	(ARG(node) != ANYOF_NONBITMAP_EMPTY)
#else
#error Unsupported PERL_API_VERSION
#endif
#endif
#endif
#endif

#define SIZEOF_ARRAY(a) (sizeof(a) / sizeof(a[0]))

#define TOLOWER(c) ((((c) >= 'A') && ((c) <= 'Z')) ? ((c) - 'A' + 'a') : (c))

#define LETTER_COUNT ('z' - 'a' + 1)

#define INFINITE_COUNT 32767

#define ALNUM_BLOCK 0x0001
#define SPACE_BLOCK 0x0002
#define ALPHA_BLOCK 0x0004
#define NUMBER_BLOCK 0x0008
#define UPPER_BLOCK 0x0010
#define LOWER_BLOCK 0x0020
#define HEX_DIGIT_BLOCK 0x0040
#define HORIZONTAL_SPACE_BLOCK 0x0080
#define VERTICAL_SPACE_BLOCK 0x0100

#define MIRROR_SHIFT 16
#define NOT_ALNUM_BLOCK (ALNUM_BLOCK << MIRROR_SHIFT)
#define NOT_SPACE_BLOCK (SPACE_BLOCK << MIRROR_SHIFT)
#define NOT_ALPHA_BLOCK (ALPHA_BLOCK << MIRROR_SHIFT)
#define NOT_NUMBER_BLOCK (NUMBER_BLOCK << MIRROR_SHIFT)
#define NOT_UPPER_BLOCK (UPPER_BLOCK << MIRROR_SHIFT)
#define NOT_LOWER_BLOCK (LOWER_BLOCK << MIRROR_SHIFT)
#define NOT_HEX_DIGIT_BLOCK (HEX_DIGIT_BLOCK << MIRROR_SHIFT)
#define NOT_HORIZONTAL_SPACE_BLOCK (HORIZONTAL_SPACE_BLOCK << MIRROR_SHIFT)
#define NOT_VERTICAL_SPACE_BLOCK (VERTICAL_SPACE_BLOCK << MIRROR_SHIFT)

#define EVERY_BLOCK 0x01ff01ff

#define FORCED_BYTE 0x01
#define FORCED_CHAR 0x02
#define FORCED_MISMATCH (FORCED_BYTE | FORCED_CHAR)

#define MIRROR_BLOCK(b) ((((b) & 0xffff) << MIRROR_SHIFT) | ((b) >> MIRROR_SHIFT))

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

static char horizontal_whitespace_expl[] = { '\t', ' ' };

static ByteClass horizontal_whitespace;

static char vertical_whitespace_expl[] = { '\r', '\v', '\f', '\n' };

static ByteClass vertical_whitespace;

static char digit_expl[10];

static ByteClass digit;

static char xdigit_expl[10 + 2 * 6];

static ByteClass xdigit;

static char ndot_expl[] = { '\n' };

static ByteClass ndot;

static char alphanumeric_expl[11 + 2 * LETTER_COUNT];

static ByteClass word_bc;

static ByteClass alnum_bc;

/* true flags for ALNUM and its subsets, 0 otherwise */
static unsigned char alphanumeric_classes[REGNODE_MAX];

/* true flags for NALNUM and its subsets, 0 otherwise */
static unsigned char non_alphanumeric_classes[REGNODE_MAX];

#ifdef RC_POSIX_NODES
static unsigned char word_posix_regclasses[_CC_VERTSPACE + 1];

static unsigned char non_word_posix_regclasses[_CC_VERTSPACE + 1];

static unsigned char newline_posix_regclasses[_CC_VERTSPACE + 1];
#endif

/* Simplified hierarchy of character classes; ignoring the difference
   between classes (i.e. IsAlnum & IsWord), which we probably
   shouldn't - it is a documented bug, though... */
static char *regclass_names[] = { "Digit", "IsAlnum", "IsSpacePerl",
				  "IsHorizSpace", "IsVertSpace",
				  "IsWord", "IsXPosixAlnum", "IsXPosixXDigit",
				  "IsAlpha", "IsXPosixAlpha",
				  "IsDigit", "IsLower", "IsUpper",
				  "IsXDigit", "SpacePerl", "VertSpace",
				  "Word", "XPosixDigit",
				  "XPosixWord", "XPosixAlpha", "XPosixAlnum",
				  "XPosixXDigit" };

static U32 regclass_blocks[] = { NUMBER_BLOCK, ALNUM_BLOCK, SPACE_BLOCK, 
				 HORIZONTAL_SPACE_BLOCK, 
				 VERTICAL_SPACE_BLOCK, ALNUM_BLOCK,
				 ALNUM_BLOCK, HEX_DIGIT_BLOCK, ALPHA_BLOCK,
				 ALPHA_BLOCK, NUMBER_BLOCK, LOWER_BLOCK,
				 UPPER_BLOCK, HEX_DIGIT_BLOCK, SPACE_BLOCK,
				 VERTICAL_SPACE_BLOCK, ALNUM_BLOCK,
				 NUMBER_BLOCK, ALNUM_BLOCK, ALPHA_BLOCK,
				 ALNUM_BLOCK, HEX_DIGIT_BLOCK};

static U32 regclass_superset[] = { NOT_SPACE_BLOCK,
				   NOT_ALPHA_BLOCK, NOT_NUMBER_BLOCK,
				   ALNUM_BLOCK, ALNUM_BLOCK,
				   ALPHA_BLOCK, ALPHA_BLOCK, HEX_DIGIT_BLOCK,
				   SPACE_BLOCK, NOT_NUMBER_BLOCK,
				   NOT_HEX_DIGIT_BLOCK };
static U32 regclass_subset[] = { ALNUM_BLOCK,
				 NOT_ALNUM_BLOCK, NOT_ALNUM_BLOCK,
				 ALPHA_BLOCK, NUMBER_BLOCK,
				 UPPER_BLOCK, LOWER_BLOCK, NUMBER_BLOCK,
				 HORIZONTAL_SPACE_BLOCK, 
				 VERTICAL_SPACE_BLOCK, VERTICAL_SPACE_BLOCK };

#ifdef RC_POSIX_NODES
static U32 posix_regclass_blocks[] = { ALNUM_BLOCK /* _CC_WORDCHAR == 0 */,
				       NUMBER_BLOCK /* _CC_DIGIT == 1 */,
				       ALPHA_BLOCK /* _CC_ALPHA == 2 */,
				       LOWER_BLOCK /* _CC_LOWER == 3 */,
				       UPPER_BLOCK /* _CC_UPPER == 4 */,
				       0,
				       0,
				       ALNUM_BLOCK /* _CC_ALPHANUMERIC == 7 */,
				       0,
				       0,
				       SPACE_BLOCK /* _CC_SPACE == 10 */,
				       HORIZONTAL_SPACE_BLOCK /* _CC_BLANK == 11, and according to perlrecharclass "\p{Blank}" and "\p{HorizSpace}" are synonyms. */,
				       HEX_DIGIT_BLOCK /* _CC_XDIGIT == 12 */,
				       0,
				       0,
				       0,
				       VERTICAL_SPACE_BLOCK /* _CC_VERTSPACE == 16 */ };

static unsigned char *posix_regclass_bitmaps[] = { word_bc.bitmap,
						   digit.bitmap,
						   0,
						   0,
						   0,
						   0,
						   0,
						   alnum_bc.bitmap,
						   0,
						   0,
						   whitespace.bitmap,
						   horizontal_whitespace.bitmap,
						   xdigit.bitmap,
						   0,
						   0,
						   0,
						   vertical_whitespace.bitmap
};

static unsigned char *posix_regclass_nbitmaps[] = { word_bc.nbitmap,
						    digit.nbitmap,
						    0,
						    0,
						    0,
						    0,
						    0,
						    alnum_bc.nbitmap,
						    0,
						    0,
						    whitespace.nbitmap,
						    horizontal_whitespace.nbitmap,
						    xdigit.nbitmap,
						    0,
						    0,
						    0,
						    vertical_whitespace.nbitmap
};
#endif

static unsigned char trivial_nodes[REGNODE_MAX];

static FCompare dispatch[REGNODE_MAX][REGNODE_MAX];

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

static U32 extend_mask(U32 mask)
{
    U32 prev_mask;
    int i, j;

    /* extra cycle is inefficient but makes superset & subset
       definitions order-independent */
    prev_mask = 0;
    while (mask != prev_mask)
    {
        prev_mask = mask;
	for (i = 0; i < 2; ++i)
	{
	    for (j = 0; j < SIZEOF_ARRAY(regclass_superset); ++j)
	    {
		U32 b = regclass_superset[j];
		U32 s = regclass_subset[j];
		if (i)
		{
		    U32 t;

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

static int convert_desc_to_map(char *desc, int invert, U32 *map)
{
    int i;
    U32 mask = 0;
    char *p;

    /* fprintf(stderr, "enter convert_desc_to_map(%s, %d\n", desc, invert); */

    p = strstr(desc, "utf8::");
    /* make sure *(p - 1) is valid */
    if (p == desc)
    {
        rc_error = "no inversion flag before character class description";
	return -1;
    }

    while (p)
    {
        char sign = *(p - 1);
	for (i = 0; i < SIZEOF_ARRAY(regclass_names); ++i)
	{
	    if (!strncmp(p + 6, regclass_names[i], strlen(regclass_names[i])))
	    {
		if (sign == '+')
		{
		    if (mask & (regclass_blocks[i] << MIRROR_SHIFT))
		    {
		        *map = invert ? 0 : EVERY_BLOCK;
			return 1;
		    }

		    mask |= regclass_blocks[i];
		}
		else if (sign == '!')
		{
		    if (mask & regclass_blocks[i])
		    {
		        *map = invert ? 0 : EVERY_BLOCK;
			return 1;
		    }

		    mask |= (regclass_blocks[i] << MIRROR_SHIFT);
		}
		else
		{
		    rc_error = "unknown inversion flag before character class description";
		    return -1;
		}
	    }
	}

	p = strstr(p + 6, "utf8::");
    }

    /* fprintf(stderr, "parsed 0x%x\n", (unsigned)mask); */

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

    *map = extend_mask(mask);
    return 1;
}

/* invlist methods are static inside regcomp.c, so we must copy them... */
#ifndef RC_INVLIST_EX
static UV *get_invlist_len_addr(SV *invlist)
{
    return (UV *)SvPVX(invlist);
}

static UV *get_invlist_zero_addr(SV *invlist)
{
    return (UV *)(SvPVX(invlist) + (3 * sizeof(UV)));
}

static UV *invlist_array(SV *invlist)
{
    return (UV *) (get_invlist_zero_addr(invlist) +
	*get_invlist_zero_addr(invlist));
}
#else
static bool *get_invlist_offset_addr(SV *invlist)
{
    return &(((XINVLIST*) SvANY(invlist))->is_offset);
}

static UV get_invlist_len(SV *invlist)
{
    return (SvCUR(invlist) == 0)
           ? 0
           : (SvCUR(invlist) / sizeof(UV)) - *get_invlist_offset_addr(invlist);
}

static UV *invlist_array(SV *invlist)
{
    return ((UV *) SvPVX(invlist) + *get_invlist_offset_addr(invlist));
}
#endif

/* #define DEBUG_dump_invlist */

static int convert_invlist_to_map(SV *invlist, int invert, U32 *map)
{
    /* 
       Not quite what's in charclass_invlists.h - we skip the header
       as well as all ASCII values.
       Note that changes to the arrays may require changing the switch
       below.
    */
    static UV perl_space_invlist[] = { 128, 133, 134, 160, 161, 5760,
        5761, 6158, 6159, 8192, 8203, 8232, 8234, 8239, 8240, 8287,
        8288, 12288, 12289 };

    static UV horizontal_space_invlist[] = { 128, 160, 161, 5760, 5761,
        6158, 6159, 8192, 8203, 8239, 8240, 8287, 8288, 12288, 12289 };

    static UV vertical_space_invlist[] = { 128, 133, 134, 8232, 8234 };

#ifdef RC_INVLIST_EX
    static UV xposix_digit_invlist[] = { 128, 1632, 1642, 1776, 1786,
	1984, 1994, 2406, 2416, 2534, 2544, 2662, 2672, 2790, 2800,
	2918, 2928, 3046, 3056, 3174, 3184, 3302, 3312, 3430, 3440,
	3664, 3674, 3792, 3802, 3872, 3882, 4160, 4170, 4240, 4250,
	6112,
	6122,
	6160,
	6170,
	6470,
	6480,
	6608,
	6618,
	6784,
	6794,
	6800,
	6810,
	6992,
	7002,
	7088,
	7098,
	7232,
	7242,
	7248,
	7258,
	42528,
	42538,
	43216,
	43226,
	43264,
	43274,
	43472,
	43482,
	43600,
	43610,
	44016,
	44026,
	65296,
	65306,
	66720,
	66730,
	69734,
	69744,
	69872,
	69882,
	69942,
	69952,
	70096,
	70106,
	71360,
	71370,
	120782,
	120832
    };

    static UV xposix_alnum_invlist[] = { 128,
	170,
	171,
	181,
	182,
	186,
	187,
	192,
	215,
	216,
	247,
	248,
	706,
	710,
	722,
	736,
	741,
	748,
	749,
	750,
	751,
	837,
	838,
	880,
	885,
	886,
	888,
	890,
	894,
	902,
	903,
	904,
	907,
	908,
	909,
	910,
	930,
	931,
	1014,
	1015,
	1154,
	1162,
	1320,
	1329,
	1367,
	1369,
	1370,
	1377,
	1416,
	1456,
	1470,
	1471,
	1472,
	1473,
	1475,
	1476,
	1478,
	1479,
	1480,
	1488,
	1515,
	1520,
	1523,
	1552,
	1563,
	1568,
	1624,
	1625,
	1642,
	1646,
	1748,
	1749,
	1757,
	1761,
	1769,
	1773,
	1789,
	1791,
	1792,
	1808,
	1856,
	1869,
	1970,
	1984,
	2027,
	2036,
	2038,
	2042,
	2043,
	2048,
	2072,
	2074,
	2093,
	2112,
	2137,
	2208,
	2209,
	2210,
	2221,
	2276,
	2282,
	2288,
	2303,
	2304,
	2364,
	2365,
	2381,
	2382,
	2385,
	2389,
	2404,
	2406,
	2416,
	2417,
	2424,
	2425,
	2432,
	2433,
	2436,
	2437,
	2445,
	2447,
	2449,
	2451,
	2473,
	2474,
	2481,
	2482,
	2483,
	2486,
	2490,
	2493,
	2501,
	2503,
	2505,
	2507,
	2509,
	2510,
	2511,
	2519,
	2520,
	2524,
	2526,
	2527,
	2532,
	2534,
	2546,
	2561,
	2564,
	2565,
	2571,
	2575,
	2577,
	2579,
	2601,
	2602,
	2609,
	2610,
	2612,
	2613,
	2615,
	2616,
	2618,
	2622,
	2627,
	2631,
	2633,
	2635,
	2637,
	2641,
	2642,
	2649,
	2653,
	2654,
	2655,
	2662,
	2678,
	2689,
	2692,
	2693,
	2702,
	2703,
	2706,
	2707,
	2729,
	2730,
	2737,
	2738,
	2740,
	2741,
	2746,
	2749,
	2758,
	2759,
	2762,
	2763,
	2765,
	2768,
	2769,
	2784,
	2788,
	2790,
	2800,
	2817,
	2820,
	2821,
	2829,
	2831,
	2833,
	2835,
	2857,
	2858,
	2865,
	2866,
	2868,
	2869,
	2874,
	2877,
	2885,
	2887,
	2889,
	2891,
	2893,
	2902,
	2904,
	2908,
	2910,
	2911,
	2916,
	2918,
	2928,
	2929,
	2930,
	2946,
	2948,
	2949,
	2955,
	2958,
	2961,
	2962,
	2966,
	2969,
	2971,
	2972,
	2973,
	2974,
	2976,
	2979,
	2981,
	2984,
	2987,
	2990,
	3002,
	3006,
	3011,
	3014,
	3017,
	3018,
	3021,
	3024,
	3025,
	3031,
	3032,
	3046,
	3056,
	3073,
	3076,
	3077,
	3085,
	3086,
	3089,
	3090,
	3113,
	3114,
	3124,
	3125,
	3130,
	3133,
	3141,
	3142,
	3145,
	3146,
	3149,
	3157,
	3159,
	3160,
	3162,
	3168,
	3172,
	3174,
	3184,
	3202,
	3204,
	3205,
	3213,
	3214,
	3217,
	3218,
	3241,
	3242,
	3252,
	3253,
	3258,
	3261,
	3269,
	3270,
	3273,
	3274,
	3277,
	3285,
	3287,
	3294,
	3295,
	3296,
	3300,
	3302,
	3312,
	3313,
	3315,
	3330,
	3332,
	3333,
	3341,
	3342,
	3345,
	3346,
	3387,
	3389,
	3397,
	3398,
	3401,
	3402,
	3405,
	3406,
	3407,
	3415,
	3416,
	3424,
	3428,
	3430,
	3440,
	3450,
	3456,
	3458,
	3460,
	3461,
	3479,
	3482,
	3506,
	3507,
	3516,
	3517,
	3518,
	3520,
	3527,
	3535,
	3541,
	3542,
	3543,
	3544,
	3552,
	3570,
	3572,
	3585,
	3643,
	3648,
	3655,
	3661,
	3662,
	3664,
	3674,
	3713,
	3715,
	3716,
	3717,
	3719,
	3721,
	3722,
	3723,
	3725,
	3726,
	3732,
	3736,
	3737,
	3744,
	3745,
	3748,
	3749,
	3750,
	3751,
	3752,
	3754,
	3756,
	3757,
	3770,
	3771,
	3774,
	3776,
	3781,
	3782,
	3783,
	3789,
	3790,
	3792,
	3802,
	3804,
	3808,
	3840,
	3841,
	3872,
	3882,
	3904,
	3912,
	3913,
	3949,
	3953,
	3970,
	3976,
	3992,
	3993,
	4029,
	4096,
	4151,
	4152,
	4153,
	4155,
	4170,
	4176,
	4195,
	4197,
	4201,
	4206,
	4231,
	4238,
	4239,
	4240,
	4250,
	4252,
	4254,
	4256,
	4294,
	4295,
	4296,
	4301,
	4302,
	4304,
	4347,
	4348,
	4681,
	4682,
	4686,
	4688,
	4695,
	4696,
	4697,
	4698,
	4702,
	4704,
	4745,
	4746,
	4750,
	4752,
	4785,
	4786,
	4790,
	4792,
	4799,
	4800,
	4801,
	4802,
	4806,
	4808,
	4823,
	4824,
	4881,
	4882,
	4886,
	4888,
	4955,
	4959,
	4960,
	4992,
	5008,
	5024,
	5109,
	5121,
	5741,
	5743,
	5760,
	5761,
	5787,
	5792,
	5867,
	5870,
	5873,
	5888,
	5901,
	5902,
	5908,
	5920,
	5940,
	5952,
	5972,
	5984,
	5997,
	5998,
	6001,
	6002,
	6004,
	6016,
	6068,
	6070,
	6089,
	6103,
	6104,
	6108,
	6109,
	6112,
	6122,
	6160,
	6170,
	6176,
	6264,
	6272,
	6315,
	6320,
	6390,
	6400,
	6429,
	6432,
	6444,
	6448,
	6457,
	6470,
	6510,
	6512,
	6517,
	6528,
	6572,
	6576,
	6602,
	6608,
	6618,
	6656,
	6684,
	6688,
	6751,
	6753,
	6773,
	6784,
	6794,
	6800,
	6810,
	6823,
	6824,
	6912,
	6964,
	6965,
	6980,
	6981,
	6988,
	6992,
	7002,
	7040,
	7082,
	7084,
	7142,
	7143,
	7154,
	7168,
	7222,
	7232,
	7242,
	7245,
	7294,
	7401,
	7405,
	7406,
	7412,
	7413,
	7415,
	7424,
	7616,
	7680,
	7958,
	7960,
	7966,
	7968,
	8006,
	8008,
	8014,
	8016,
	8024,
	8025,
	8026,
	8027,
	8028,
	8029,
	8030,
	8031,
	8062,
	8064,
	8117,
	8118,
	8125,
	8126,
	8127,
	8130,
	8133,
	8134,
	8141,
	8144,
	8148,
	8150,
	8156,
	8160,
	8173,
	8178,
	8181,
	8182,
	8189,
	8305,
	8306,
	8319,
	8320,
	8336,
	8349,
	8450,
	8451,
	8455,
	8456,
	8458,
	8468,
	8469,
	8470,
	8473,
	8478,
	8484,
	8485,
	8486,
	8487,
	8488,
	8489,
	8490,
	8494,
	8495,
	8506,
	8508,
	8512,
	8517,
	8522,
	8526,
	8527,
	8544,
	8585,
	9398,
	9450,
	11264,
	11311,
	11312,
	11359,
	11360,
	11493,
	11499,
	11503,
	11506,
	11508,
	11520,
	11558,
	11559,
	11560,
	11565,
	11566,
	11568,
	11624,
	11631,
	11632,
	11648,
	11671,
	11680,
	11687,
	11688,
	11695,
	11696,
	11703,
	11704,
	11711,
	11712,
	11719,
	11720,
	11727,
	11728,
	11735,
	11736,
	11743,
	11744,
	11776,
	11823,
	11824,
	12293,
	12296,
	12321,
	12330,
	12337,
	12342,
	12344,
	12349,
	12353,
	12439,
	12445,
	12448,
	12449,
	12539,
	12540,
	12544,
	12549,
	12590,
	12593,
	12687,
	12704,
	12731,
	12784,
	12800,
	13312,
	19894,
	19968,
	40909,
	40960,
	42125,
	42192,
	42238,
	42240,
	42509,
	42512,
	42540,
	42560,
	42607,
	42612,
	42620,
	42623,
	42648,
	42655,
	42736,
	42775,
	42784,
	42786,
	42889,
	42891,
	42895,
	42896,
	42900,
	42912,
	42923,
	43000,
	43010,
	43011,
	43014,
	43015,
	43019,
	43020,
	43048,
	43072,
	43124,
	43136,
	43204,
	43216,
	43226,
	43250,
	43256,
	43259,
	43260,
	43264,
	43307,
	43312,
	43347,
	43360,
	43389,
	43392,
	43443,
	43444,
	43456,
	43471,
	43482,
	43520,
	43575,
	43584,
	43598,
	43600,
	43610,
	43616,
	43639,
	43642,
	43643,
	43648,
	43711,
	43712,
	43713,
	43714,
	43715,
	43739,
	43742,
	43744,
	43760,
	43762,
	43766,
	43777,
	43783,
	43785,
	43791,
	43793,
	43799,
	43808,
	43815,
	43816,
	43823,
	43968,
	44011,
	44016,
	44026,
	44032,
	55204,
	55216,
	55239,
	55243,
	55292,
	63744,
	64110,
	64112,
	64218,
	64256,
	64263,
	64275,
	64280,
	64285,
	64297,
	64298,
	64311,
	64312,
	64317,
	64318,
	64319,
	64320,
	64322,
	64323,
	64325,
	64326,
	64434,
	64467,
	64830,
	64848,
	64912,
	64914,
	64968,
	65008,
	65020,
	65136,
	65141,
	65142,
	65277,
	65296,
	65306,
	65313,
	65339,
	65345,
	65371,
	65382,
	65471,
	65474,
	65480,
	65482,
	65488,
	65490,
	65496,
	65498,
	65501,
	65536,
	65548,
	65549,
	65575,
	65576,
	65595,
	65596,
	65598,
	65599,
	65614,
	65616,
	65630,
	65664,
	65787,
	65856,
	65909,
	66176,
	66205,
	66208,
	66257,
	66304,
	66335,
	66352,
	66379,
	66432,
	66462,
	66464,
	66500,
	66504,
	66512,
	66513,
	66518,
	66560,
	66718,
	66720,
	66730,
	67584,
	67590,
	67592,
	67593,
	67594,
	67638,
	67639,
	67641,
	67644,
	67645,
	67647,
	67670,
	67840,
	67862,
	67872,
	67898,
	67968,
	68024,
	68030,
	68032,
	68096,
	68100,
	68101,
	68103,
	68108,
	68116,
	68117,
	68120,
	68121,
	68148,
	68192,
	68221,
	68352,
	68406,
	68416,
	68438,
	68448,
	68467,
	68608,
	68681,
	69632,
	69702,
	69734,
	69744,
	69762,
	69817,
	69840,
	69865,
	69872,
	69882,
	69888,
	69939,
	69942,
	69952,
	70016,
	70080,
	70081,
	70085,
	70096,
	70106,
	71296,
	71350,
	71360,
	71370,
	73728,
	74607,
	74752,
	74851,
	77824,
	78895,
	92160,
	92729,
	93952,
	94021,
	94032,
	94079,
	94099,
	94112,
	110592,
	110594,
	119808,
	119893,
	119894,
	119965,
	119966,
	119968,
	119970,
	119971,
	119973,
	119975,
	119977,
	119981,
	119982,
	119994,
	119995,
	119996,
	119997,
	120004,
	120005,
	120070,
	120071,
	120075,
	120077,
	120085,
	120086,
	120093,
	120094,
	120122,
	120123,
	120127,
	120128,
	120133,
	120134,
	120135,
	120138,
	120145,
	120146,
	120486,
	120488,
	120513,
	120514,
	120539,
	120540,
	120571,
	120572,
	120597,
	120598,
	120629,
	120630,
	120655,
	120656,
	120687,
	120688,
	120713,
	120714,
	120745,
	120746,
	120771,
	120772,
	120780,
	120782,
	120832,
	126464,
	126468,
	126469,
	126496,
	126497,
	126499,
	126500,
	126501,
	126503,
	126504,
	126505,
	126515,
	126516,
	126520,
	126521,
	126522,
	126523,
	126524,
	126530,
	126531,
	126535,
	126536,
	126537,
	126538,
	126539,
	126540,
	126541,
	126544,
	126545,
	126547,
	126548,
	126549,
	126551,
	126552,
	126553,
	126554,
	126555,
	126556,
	126557,
	126558,
	126559,
	126560,
	126561,
	126563,
	126564,
	126565,
	126567,
	126571,
	126572,
	126579,
	126580,
	126584,
	126585,
	126589,
	126590,
	126591,
	126592,
	126602,
	126603,
	126620,
	126625,
	126628,
	126629,
	126634,
	126635,
	126652,
	131072,
	173783,
	173824,
	177973,
	177984,
	178206,
	194560,
	195102
};

    static UV xposix_word_invlist[] = { 128,
	170,
	171,
	181,
	182,
	186,
	187,
	192,
	215,
	216,
	247,
	248,
	706,
	710,
	722,
	736,
	741,
	748,
	749,
	750,
	751,
	768,
	885,
	886,
	888,
	890,
	894,
	902,
	903,
	904,
	907,
	908,
	909,
	910,
	930,
	931,
	1014,
	1015,
	1154,
	1155,
	1320,
	1329,
	1367,
	1369,
	1370,
	1377,
	1416,
	1425,
	1470,
	1471,
	1472,
	1473,
	1475,
	1476,
	1478,
	1479,
	1480,
	1488,
	1515,
	1520,
	1523,
	1552,
	1563,
	1568,
	1642,
	1646,
	1748,
	1749,
	1757,
	1759,
	1769,
	1770,
	1789,
	1791,
	1792,
	1808,
	1867,
	1869,
	1970,
	1984,
	2038,
	2042,
	2043,
	2048,
	2094,
	2112,
	2140,
	2208,
	2209,
	2210,
	2221,
	2276,
	2303,
	2304,
	2404,
	2406,
	2416,
	2417,
	2424,
	2425,
	2432,
	2433,
	2436,
	2437,
	2445,
	2447,
	2449,
	2451,
	2473,
	2474,
	2481,
	2482,
	2483,
	2486,
	2490,
	2492,
	2501,
	2503,
	2505,
	2507,
	2511,
	2519,
	2520,
	2524,
	2526,
	2527,
	2532,
	2534,
	2546,
	2561,
	2564,
	2565,
	2571,
	2575,
	2577,
	2579,
	2601,
	2602,
	2609,
	2610,
	2612,
	2613,
	2615,
	2616,
	2618,
	2620,
	2621,
	2622,
	2627,
	2631,
	2633,
	2635,
	2638,
	2641,
	2642,
	2649,
	2653,
	2654,
	2655,
	2662,
	2678,
	2689,
	2692,
	2693,
	2702,
	2703,
	2706,
	2707,
	2729,
	2730,
	2737,
	2738,
	2740,
	2741,
	2746,
	2748,
	2758,
	2759,
	2762,
	2763,
	2766,
	2768,
	2769,
	2784,
	2788,
	2790,
	2800,
	2817,
	2820,
	2821,
	2829,
	2831,
	2833,
	2835,
	2857,
	2858,
	2865,
	2866,
	2868,
	2869,
	2874,
	2876,
	2885,
	2887,
	2889,
	2891,
	2894,
	2902,
	2904,
	2908,
	2910,
	2911,
	2916,
	2918,
	2928,
	2929,
	2930,
	2946,
	2948,
	2949,
	2955,
	2958,
	2961,
	2962,
	2966,
	2969,
	2971,
	2972,
	2973,
	2974,
	2976,
	2979,
	2981,
	2984,
	2987,
	2990,
	3002,
	3006,
	3011,
	3014,
	3017,
	3018,
	3022,
	3024,
	3025,
	3031,
	3032,
	3046,
	3056,
	3073,
	3076,
	3077,
	3085,
	3086,
	3089,
	3090,
	3113,
	3114,
	3124,
	3125,
	3130,
	3133,
	3141,
	3142,
	3145,
	3146,
	3150,
	3157,
	3159,
	3160,
	3162,
	3168,
	3172,
	3174,
	3184,
	3202,
	3204,
	3205,
	3213,
	3214,
	3217,
	3218,
	3241,
	3242,
	3252,
	3253,
	3258,
	3260,
	3269,
	3270,
	3273,
	3274,
	3278,
	3285,
	3287,
	3294,
	3295,
	3296,
	3300,
	3302,
	3312,
	3313,
	3315,
	3330,
	3332,
	3333,
	3341,
	3342,
	3345,
	3346,
	3387,
	3389,
	3397,
	3398,
	3401,
	3402,
	3407,
	3415,
	3416,
	3424,
	3428,
	3430,
	3440,
	3450,
	3456,
	3458,
	3460,
	3461,
	3479,
	3482,
	3506,
	3507,
	3516,
	3517,
	3518,
	3520,
	3527,
	3530,
	3531,
	3535,
	3541,
	3542,
	3543,
	3544,
	3552,
	3570,
	3572,
	3585,
	3643,
	3648,
	3663,
	3664,
	3674,
	3713,
	3715,
	3716,
	3717,
	3719,
	3721,
	3722,
	3723,
	3725,
	3726,
	3732,
	3736,
	3737,
	3744,
	3745,
	3748,
	3749,
	3750,
	3751,
	3752,
	3754,
	3756,
	3757,
	3770,
	3771,
	3774,
	3776,
	3781,
	3782,
	3783,
	3784,
	3790,
	3792,
	3802,
	3804,
	3808,
	3840,
	3841,
	3864,
	3866,
	3872,
	3882,
	3893,
	3894,
	3895,
	3896,
	3897,
	3898,
	3902,
	3912,
	3913,
	3949,
	3953,
	3973,
	3974,
	3992,
	3993,
	4029,
	4038,
	4039,
	4096,
	4170,
	4176,
	4254,
	4256,
	4294,
	4295,
	4296,
	4301,
	4302,
	4304,
	4347,
	4348,
	4681,
	4682,
	4686,
	4688,
	4695,
	4696,
	4697,
	4698,
	4702,
	4704,
	4745,
	4746,
	4750,
	4752,
	4785,
	4786,
	4790,
	4792,
	4799,
	4800,
	4801,
	4802,
	4806,
	4808,
	4823,
	4824,
	4881,
	4882,
	4886,
	4888,
	4955,
	4957,
	4960,
	4992,
	5008,
	5024,
	5109,
	5121,
	5741,
	5743,
	5760,
	5761,
	5787,
	5792,
	5867,
	5870,
	5873,
	5888,
	5901,
	5902,
	5909,
	5920,
	5941,
	5952,
	5972,
	5984,
	5997,
	5998,
	6001,
	6002,
	6004,
	6016,
	6100,
	6103,
	6104,
	6108,
	6110,
	6112,
	6122,
	6155,
	6158,
	6160,
	6170,
	6176,
	6264,
	6272,
	6315,
	6320,
	6390,
	6400,
	6429,
	6432,
	6444,
	6448,
	6460,
	6470,
	6510,
	6512,
	6517,
	6528,
	6572,
	6576,
	6602,
	6608,
	6618,
	6656,
	6684,
	6688,
	6751,
	6752,
	6781,
	6783,
	6794,
	6800,
	6810,
	6823,
	6824,
	6912,
	6988,
	6992,
	7002,
	7019,
	7028,
	7040,
	7156,
	7168,
	7224,
	7232,
	7242,
	7245,
	7294,
	7376,
	7379,
	7380,
	7415,
	7424,
	7655,
	7676,
	7958,
	7960,
	7966,
	7968,
	8006,
	8008,
	8014,
	8016,
	8024,
	8025,
	8026,
	8027,
	8028,
	8029,
	8030,
	8031,
	8062,
	8064,
	8117,
	8118,
	8125,
	8126,
	8127,
	8130,
	8133,
	8134,
	8141,
	8144,
	8148,
	8150,
	8156,
	8160,
	8173,
	8178,
	8181,
	8182,
	8189,
	8204,
	8206,
	8255,
	8257,
	8276,
	8277,
	8305,
	8306,
	8319,
	8320,
	8336,
	8349,
	8400,
	8433,
	8450,
	8451,
	8455,
	8456,
	8458,
	8468,
	8469,
	8470,
	8473,
	8478,
	8484,
	8485,
	8486,
	8487,
	8488,
	8489,
	8490,
	8494,
	8495,
	8506,
	8508,
	8512,
	8517,
	8522,
	8526,
	8527,
	8544,
	8585,
	9398,
	9450,
	11264,
	11311,
	11312,
	11359,
	11360,
	11493,
	11499,
	11508,
	11520,
	11558,
	11559,
	11560,
	11565,
	11566,
	11568,
	11624,
	11631,
	11632,
	11647,
	11671,
	11680,
	11687,
	11688,
	11695,
	11696,
	11703,
	11704,
	11711,
	11712,
	11719,
	11720,
	11727,
	11728,
	11735,
	11736,
	11743,
	11744,
	11776,
	11823,
	11824,
	12293,
	12296,
	12321,
	12336,
	12337,
	12342,
	12344,
	12349,
	12353,
	12439,
	12441,
	12443,
	12445,
	12448,
	12449,
	12539,
	12540,
	12544,
	12549,
	12590,
	12593,
	12687,
	12704,
	12731,
	12784,
	12800,
	13312,
	19894,
	19968,
	40909,
	40960,
	42125,
	42192,
	42238,
	42240,
	42509,
	42512,
	42540,
	42560,
	42611,
	42612,
	42622,
	42623,
	42648,
	42655,
	42738,
	42775,
	42784,
	42786,
	42889,
	42891,
	42895,
	42896,
	42900,
	42912,
	42923,
	43000,
	43048,
	43072,
	43124,
	43136,
	43205,
	43216,
	43226,
	43232,
	43256,
	43259,
	43260,
	43264,
	43310,
	43312,
	43348,
	43360,
	43389,
	43392,
	43457,
	43471,
	43482,
	43520,
	43575,
	43584,
	43598,
	43600,
	43610,
	43616,
	43639,
	43642,
	43644,
	43648,
	43715,
	43739,
	43742,
	43744,
	43760,
	43762,
	43767,
	43777,
	43783,
	43785,
	43791,
	43793,
	43799,
	43808,
	43815,
	43816,
	43823,
	43968,
	44011,
	44012,
	44014,
	44016,
	44026,
	44032,
	55204,
	55216,
	55239,
	55243,
	55292,
	63744,
	64110,
	64112,
	64218,
	64256,
	64263,
	64275,
	64280,
	64285,
	64297,
	64298,
	64311,
	64312,
	64317,
	64318,
	64319,
	64320,
	64322,
	64323,
	64325,
	64326,
	64434,
	64467,
	64830,
	64848,
	64912,
	64914,
	64968,
	65008,
	65020,
	65024,
	65040,
	65056,
	65063,
	65075,
	65077,
	65101,
	65104,
	65136,
	65141,
	65142,
	65277,
	65296,
	65306,
	65313,
	65339,
	65343,
	65344,
	65345,
	65371,
	65382,
	65471,
	65474,
	65480,
	65482,
	65488,
	65490,
	65496,
	65498,
	65501,
	65536,
	65548,
	65549,
	65575,
	65576,
	65595,
	65596,
	65598,
	65599,
	65614,
	65616,
	65630,
	65664,
	65787,
	65856,
	65909,
	66045,
	66046,
	66176,
	66205,
	66208,
	66257,
	66304,
	66335,
	66352,
	66379,
	66432,
	66462,
	66464,
	66500,
	66504,
	66512,
	66513,
	66518,
	66560,
	66718,
	66720,
	66730,
	67584,
	67590,
	67592,
	67593,
	67594,
	67638,
	67639,
	67641,
	67644,
	67645,
	67647,
	67670,
	67840,
	67862,
	67872,
	67898,
	67968,
	68024,
	68030,
	68032,
	68096,
	68100,
	68101,
	68103,
	68108,
	68116,
	68117,
	68120,
	68121,
	68148,
	68152,
	68155,
	68159,
	68160,
	68192,
	68221,
	68352,
	68406,
	68416,
	68438,
	68448,
	68467,
	68608,
	68681,
	69632,
	69703,
	69734,
	69744,
	69760,
	69819,
	69840,
	69865,
	69872,
	69882,
	69888,
	69941,
	69942,
	69952,
	70016,
	70085,
	70096,
	70106,
	71296,
	71352,
	71360,
	71370,
	73728,
	74607,
	74752,
	74851,
	77824,
	78895,
	92160,
	92729,
	93952,
	94021,
	94032,
	94079,
	94095,
	94112,
	110592,
	110594,
	119141,
	119146,
	119149,
	119155,
	119163,
	119171,
	119173,
	119180,
	119210,
	119214,
	119362,
	119365,
	119808,
	119893,
	119894,
	119965,
	119966,
	119968,
	119970,
	119971,
	119973,
	119975,
	119977,
	119981,
	119982,
	119994,
	119995,
	119996,
	119997,
	120004,
	120005,
	120070,
	120071,
	120075,
	120077,
	120085,
	120086,
	120093,
	120094,
	120122,
	120123,
	120127,
	120128,
	120133,
	120134,
	120135,
	120138,
	120145,
	120146,
	120486,
	120488,
	120513,
	120514,
	120539,
	120540,
	120571,
	120572,
	120597,
	120598,
	120629,
	120630,
	120655,
	120656,
	120687,
	120688,
	120713,
	120714,
	120745,
	120746,
	120771,
	120772,
	120780,
	120782,
	120832,
	126464,
	126468,
	126469,
	126496,
	126497,
	126499,
	126500,
	126501,
	126503,
	126504,
	126505,
	126515,
	126516,
	126520,
	126521,
	126522,
	126523,
	126524,
	126530,
	126531,
	126535,
	126536,
	126537,
	126538,
	126539,
	126540,
	126541,
	126544,
	126545,
	126547,
	126548,
	126549,
	126551,
	126552,
	126553,
	126554,
	126555,
	126556,
	126557,
	126558,
	126559,
	126560,
	126561,
	126563,
	126564,
	126565,
	126567,
	126571,
	126572,
	126579,
	126580,
	126584,
	126585,
	126589,
	126590,
	126591,
	126592,
	126602,
	126603,
	126620,
	126625,
	126628,
	126629,
	126634,
	126635,
	126652,
	131072,
	173783,
	173824,
	177973,
	177984,
	178206,
	194560,
	195102,
	917760,
	918000
};
#endif

    static UV xposix_xdigit_invlist[] = { 128, 65296, 65306, 65313,
        65319, 65345, 65351 };

#ifdef DEBUG_dump_invlist
    U16 i;
    char div[3];
#endif

    UV *ila;
    UV ill;
    U32 mask = 0;

#ifdef DEBUG_dump_invlist
    fprintf(stderr, "enter convert_invlist_to_map(..., %d, ...)\n", invert);
#endif

#ifndef RC_INVLIST_EX
    ill = *get_invlist_len_addr(invlist);
    ila = invlist_array(invlist);
#else
    ill = get_invlist_len(invlist);
    ila = ill ? invlist_array(invlist) : 0;
#endif

    switch (ill)
    {
    case SIZEOF_ARRAY(perl_space_invlist):
        if (!memcmp(ila, perl_space_invlist, sizeof(perl_space_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_SPACE_BLOCK\n");
#endif
	    mask = NOT_SPACE_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(perl_space_invlist) - 1:
        if (!memcmp(ila, perl_space_invlist + 1,
            sizeof(perl_space_invlist) - sizeof(perl_space_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "SPACE_BLOCK\n");
#endif
	    mask = SPACE_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(horizontal_space_invlist):
        if (!memcmp(ila, horizontal_space_invlist, sizeof(horizontal_space_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_HORIZONTAL_SPACE_BLOCK\n");
#endif
	    mask = NOT_HORIZONTAL_SPACE_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(horizontal_space_invlist) - 1:
        if (!memcmp(ila, horizontal_space_invlist + 1,
            sizeof(horizontal_space_invlist) - sizeof(horizontal_space_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "HORIZONTAL_SPACE_BLOCK\n");
#endif
	    mask = HORIZONTAL_SPACE_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(vertical_space_invlist):
        if (!memcmp(ila, vertical_space_invlist, sizeof(vertical_space_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_VERTICAL_SPACE_BLOCK\n");
#endif
	    mask = NOT_VERTICAL_SPACE_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(vertical_space_invlist) - 1:
        if (!memcmp(ila, vertical_space_invlist + 1,
            sizeof(vertical_space_invlist) - sizeof(vertical_space_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "VERTICAL_SPACE_BLOCK\n");
#endif
	    mask = VERTICAL_SPACE_BLOCK;
	}

        break;

#ifdef RC_INVLIST_EX
    case SIZEOF_ARRAY(xposix_digit_invlist):
        if (!memcmp(ila, xposix_digit_invlist, sizeof(xposix_digit_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_NUMBER_BLOCK\n");
#endif
	    mask = NOT_NUMBER_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_digit_invlist) - 1:
        if (!memcmp(ila, xposix_digit_invlist + 1,
            sizeof(xposix_digit_invlist) - sizeof(xposix_digit_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NUMBER_BLOCK\n");
#endif
	    mask = NUMBER_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_alnum_invlist):
        if (!memcmp(ila, xposix_alnum_invlist, sizeof(xposix_alnum_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_ALNUM_BLOCK\n");
#endif
	    mask = NOT_ALNUM_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_alnum_invlist) - 1:
        if (!memcmp(ila, xposix_alnum_invlist + 1,
            sizeof(xposix_alnum_invlist) - sizeof(xposix_alnum_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "ALNUM_BLOCK\n");
#endif
	    mask = ALNUM_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_word_invlist):
        if (!memcmp(ila, xposix_word_invlist, sizeof(xposix_word_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_ALPHA_BLOCK\n");
#endif
	    mask = NOT_ALPHA_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_word_invlist) - 1:
        if (!memcmp(ila, xposix_word_invlist + 1,
            sizeof(xposix_word_invlist) - sizeof(xposix_word_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "ALPHA_BLOCK\n");
#endif
	    mask = ALPHA_BLOCK;
	}

        break;

#endif
    case SIZEOF_ARRAY(xposix_xdigit_invlist):
        if (!memcmp(ila, xposix_xdigit_invlist, sizeof(xposix_xdigit_invlist)))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NOT_NUMBER_BLOCK\n");
#endif
	    mask = NOT_NUMBER_BLOCK;
	}

        break;

    case SIZEOF_ARRAY(xposix_xdigit_invlist) - 1:
        if (!memcmp(ila, xposix_xdigit_invlist + 1,
            sizeof(xposix_xdigit_invlist) - sizeof(xposix_xdigit_invlist[0])))
	{
#ifdef DEBUG_dump_invlist
	    fprintf(stderr, "NUMBER_BLOCK\n");
#endif
	    mask = NUMBER_BLOCK;
	}

        break;
    }

    if (mask)
    {
        if (invert)
	{
	    mask = MIRROR_BLOCK(mask);
	}

	*map = extend_mask(mask);
	return 1;
    }

#ifdef DEBUG_dump_invlist
    div[0] = '{';
    div[1] = ' ';
    div[2] = 0;
    for (i = 0; i < ill; ++i)
    {
        fprintf(stderr, "%s%d", div, (int)(ila[i]));
	div[0] = ',';
    }

    fprintf(stderr, " }\n");
#endif

    return 0;
}

static int convert_regclass_map(Arrow *a, U32 *map)
{
    regexp_internal *pr;
    U32 n;
    struct reg_data *rdata;

    /* fprintf(stderr, "enter convert_regclass_map\n"); */

    assert(a->rn->type == ANYOF);
    assert(ANYOF_NONBITMAP(a->rn));

    /* basically copied from regexec.c:regclass_swash */
    n = ARG_LOC(a->rn);
    pr = RXi_GET(a->origin);
    if (!pr) /* this should have been tested by find_internal during
		initialization, but just in case... */
    {
        rc_error = "regexp_internal not found";
	return -1;
    }

    rdata = pr->data;

    if ((n < rdata->count) &&
	(rdata->what[n] == 's')) {
        SV *rv = (SV *)(rdata->data[n]);
	AV *av = (AV *)SvRV(rv);
	SV **ary = AvARRAY(av);
	SV *si = *ary;

	if (si && (si != &PL_sv_undef))
        {
	    /* From regcomp.c:regclass: the 0th element stores the
	       character class description in its textual form. It isn't
	       very clear what exactly the textual form is, but we hope
	       it's 0-terminated. */
	  return convert_desc_to_map(SvPV_nolen(*ary),
	      !!(a->rn->flags & ANYOF_INVERT),
	      map);
	}
/* FIXME: in perl 5.18, crashes for inverted classes */
	else
	{
	    /* in perl 5.16, the textual form doesn't necessarily exist... */
	    if (av_len(av) >= 3)
	    {
	        SV *invlist = ary[3];

		if (SvUV(ary[4])) /* invlist_has_user_defined_property */
		{
		    /* fprintf(stderr, "invlist has user defined property\n"); */
		    return 0;
		}

		return convert_invlist_to_map(invlist,
		    !!(a->rn->flags & ANYOF_INVERT),
                    map);
	    }

	    /* fprintf(stderr, "regclass invlist not found\n"); */
	    return 0;
	}
    }

    rc_error = "regclass not found";
    return -1;
}

/* returns 1 OK (map set), 0 map not recognized/representable, -1
   unexpected input (rc_error set) */
static int convert_map(Arrow *a, U32 *map)
{
    /* fprintf(stderr, "enter convert_map\n"); */

    assert(a->rn->type == ANYOF);
    assert(map);

    if (ANYOF_NONBITMAP(a->rn))
    {
        return convert_regclass_map(a, map);
    }
    else
    {
        /* fprintf(stderr, "zero map\n"); */
	*map = 0;
	return 1;
    }
}

#ifdef RC_POSIX_NODES
/* returns 1 OK (map set), 0 map not recognized/representable */
static int convert_class_narrow(Arrow *a, U32 *map)
{
    /* fprintf(stderr, "enter convert_class_narrow\n"); */

    assert(map);

    if (a->rn->flags >= SIZEOF_ARRAY(posix_regclass_blocks))
    {
        /* fprintf(stderr, "unknown class %d\n", a->rn->flags); */
        return 0;
    }

    U32 mask = posix_regclass_blocks[a->rn->flags];
    if (!mask)
    {
        /* fprintf(stderr, "class %d ignored\n", a->rn->flags); */
	return 0;
    }

    *map = mask;
    return 1;
}

/* returns 1 OK (map set), 0 map not recognized/representable */
static int convert_class(Arrow *a, U32 *map)
{
    if (!convert_class_narrow(a, map))
    {
        return 0;
    }

    *map = extend_mask(*map);
    return 1;
}

static int convert_negative_class(Arrow *a, U32 *map)
{
    U32 mask;

    if (!convert_class_narrow(a, &mask))
    {
        return 0;
    }

    *map = extend_mask(MIRROR_BLOCK(mask));
    return 1;
}
#endif

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

    if (((p->type == EXACT) || (p->type == EXACTF) || (p->type == EXACTFU)) &&
	(p->flags == 1))
    {
	return 2;
    }
    else if (trivial_nodes[p->type] ||
	     (p->type == REG_ANY) || (p->type == SANY) ||
#ifndef RC_POSIX_NODES
	     (p->type == ALNUM) || (p->type == ALNUMA) ||
	     (p->type == NALNUM) || (p->type == NALNUMA) ||
	     (p->type == SPACE) || (p->type == SPACEA) ||
	     (p->type == NSPACE) || (p->type == NSPACEA) ||
	     (p->type == DIGIT) || (p->type == DIGITA) ||
	     (p->type == NDIGIT) || (p->type == NDIGITA) ||
	     (p->type == VERTWS) || (p->type == NVERTWS) ||
	     (p->type == HORIZWS) || (p->type == NHORIZWS)
#else
	     (p->type == POSIXD) || (p->type == NPOSIXD) ||
	     (p->type == POSIXU) || (p->type == NPOSIXU) ||
	     (p->type == POSIXA) || (p->type == NPOSIXA)
#endif
	     )
    {
	return 1;  
    }
    else if (p->type == ANYOF)
    {
        /* other flags obviously exist, but they haven't been seen yet
	   and it isn't clear what they mean */
        unsigned int unknown = p->flags & ~(ANYOF_INVERT |
	    ANYOF_LARGE | ANYOF_UNICODE_ALL | RC_ANYOF_UTF8);
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
		else if ((i + 1 < prelen) &&
		    (precomp[i + 1] == '{'))
		{
		    forced |= FORCED_CHAR;
		}

		/* otherwise it's not an escape, but the inverse of \n
		   - we aren't interested in that */

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
    if ((last >= REGNODE_MAX) || !trivial_nodes[last])
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

    assert((a->rn->type == EXACT) || (a->rn->type == EXACTF) || (a->rn->type == EXACTFU));

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
    else if ((a->rn->type == EXACT) || (a->rn->type == EXACTF) || (a->rn->type == EXACTFU))
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

REGEXP *rc_regcomp(SV *rs)
{
    REGEXP *rx;

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

void rc_regfree(REGEXP *rx)
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

    sz = (((a1->rn->flags & ANYOF_INVERT) &&
	    (a1->rn->flags & ANYOF_NON_UTF8_LATIN1_ALL)) ||
	(!(a2->rn->flags & ANYOF_INVERT) &&
	    (a2->rn->flags & ANYOF_NON_UTF8_LATIN1_ALL))) ? 16
        : ANYOF_BITMAP_SIZE;
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

    if (a1->rn->flags & ANYOF_UNICODE_ALL)
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

    extra_left = ANYOF_NONBITMAP(a1->rn);
    if ((extra_left || (a1->rn->flags & ANYOF_UNICODE_ALL)) &&
	!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 m1, m2;
	int cr1, cr2;

	cr1 = convert_map(a1, &m1);
	if (cr1 == -1)
	{
	    return -1;
	}

	cr2 = convert_map(a2, &m2);
	if (cr2 == -1)
	{
	    return -1;
	}

	/* clearly this hould happen at a lower level, but there it
	   breaks other paths... */
	if (m2 & NOT_ALNUM_BLOCK)
	{
	    m2 |= NOT_ALPHA_BLOCK | NOT_NUMBER_BLOCK;
	    m2 = extend_mask(m2);
	}

	if (!cr1 || !cr2 || (m1 & ~m2))
	{
            /* fprintf(stderr, "cr1 = %d, cr2 = %d, m1 = 0x%x, m2 = 0x%x\n",
                cr1, cr2, (unsigned)m1, (unsigned)m2); */
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

#ifndef RC_POSIX_NODES
static int compare_alnum_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ALNUM);
    assert(a2->rn->type == ANYOF);

    /* fprintf(stderr, "flags = 0x%x\n", a2->rn->flags); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & ALNUM_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, word_bc.bitmap, 0);
}

static int compare_alnuma_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ALNUMA);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, word_bc.bitmap, 0);
}

static int compare_nalnum_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NALNUM);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NOT_ALNUM_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, word_bc.nbitmap, 0);
}

static int compare_nalnuma_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NALNUMA);
    assert(a2->rn->type == ANYOF);

    /* from perlre: all non-ASCII characters match ... "\W" */
    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, word_bc.nbitmap, 0);
}

static int compare_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == SPACE) || (a1->rn->type == SPACEA));
    assert(a2->rn->type == ANYOF);

    return compare_short_byte_class(anchored, a1, a2,  &whitespace);
}

static int compare_nspace_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NSPACE);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NOT_SPACE_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, whitespace.nbitmap, 0);
}

static int compare_nspacea_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NSPACEA);
    assert(a2->rn->type == ANYOF);

    /* from perlre: all non-ASCII characters match ... "\S" */
    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, whitespace.nbitmap, 0);
}

static int compare_horizontal_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == HORIZWS);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & HORIZONTAL_SPACE_BLOCK))
	{
	    /* fprintf(stderr, "cr = %d, map = 0x%x\n", cr, (unsigned)map); */
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_short_byte_class(anchored, a1, a2,  &horizontal_whitespace);
}

static int compare_negative_horizontal_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NHORIZWS);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NOT_HORIZONTAL_SPACE_BLOCK))
	{
	    /* fprintf(stderr, "cr = %d, map = 0x%x\n", cr, (unsigned)map); */
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, horizontal_whitespace.nbitmap, 0);
}

static int compare_vertical_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == VERTWS);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & VERTICAL_SPACE_BLOCK))
	{
	    /* fprintf(stderr, "cr = %d, map = 0x%x\n", cr, (unsigned)map); */
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_short_byte_class(anchored, a1, a2,  &vertical_whitespace);
}

static int compare_negative_vertical_space_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NVERTWS);
    assert(a2->rn->type == ANYOF);

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NOT_VERTICAL_SPACE_BLOCK))
	{
	    /* fprintf(stderr, "cr = %d, map = 0x%x\n", cr, (unsigned)map); */
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, vertical_whitespace.nbitmap, 0);
}
#else
static int compare_posix_posix(int anchored, Arrow *a1, Arrow *a2)
{
    U32 m1, m2;
    int cr1, cr2;

    /* fprintf(stderr, "enter compare_posix_posix\n"); */

    cr1 = convert_class(a1, &m1);
    cr2 = convert_class(a2, &m2);
    if (!cr1 || !cr2 || (m1 & ~m2))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_posix_negative_posix(int anchored, Arrow *a1, Arrow *a2)
{
    U32 m1, m2;
    int cr1, cr2;

    /* fprintf(stderr, "enter compare_posix_negative_posix\n"); */

    cr1 = convert_class(a1, &m1);
    cr2 = convert_class(a2, &m2);
    if (!cr1 || !cr2)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    /* vertical space is not a strict subset of space, but it does
       have space elements, so we have to require space on the right */
    if ((m1 & VERTICAL_SPACE_BLOCK) && !(m2 & VERTICAL_SPACE_BLOCK))
    {
	m1 |= SPACE_BLOCK;
    }

    if (m1 & m2)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_negative_posix_negative_posix(int anchored, Arrow *a1, Arrow *a2)
{
    U32 m1, m2;
    int cr1, cr2;

    assert((a1->rn->type == NPOSIXD) || (a1->rn->type == NPOSIXU) ||
	(a1->rn->type == NPOSIXA));
    assert((a2->rn->type == NPOSIXD) || (a2->rn->type == NPOSIXU) ||
	(a2->rn->type == NPOSIXA));

    /* fprintf(stderr, "enter compare_negative_posix_negative_posix\n"); */

    cr1 = convert_negative_class(a1, &m1);
    cr2 = convert_negative_class(a2, &m2);
    if (!cr2 || !cr2 || (m1 & ~m2))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_posix(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) ||
	(a1->rn->type == EXACTFU));
    assert((a2->rn->type == POSIXD) || (a2->rn->type == POSIXU) ||
	(a2->rn->type == POSIXA));

    seq = GET_LITERAL(a1);

    if (!_generic_isCC_A(*seq, a2->rn->flags))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_posix(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    char unf[2];
    int i;

    assert((a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
    assert(a2->rn->type == POSIXD);

    seq = GET_LITERAL(a1);
    init_unfolded(unf, *seq);

    for (i = 0; i < 2; ++i)
    {
	if (!_generic_isCC_A(unf[i], a2->rn->flags))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_negative_posix(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;

    assert(a1->rn->type == EXACT);
    assert((a2->rn->type == NPOSIXD) || (a2->rn->type == NPOSIXU) ||
	(a2->rn->type == NPOSIXA));

    seq = GET_LITERAL(a1);

    if (_generic_isCC_A(*seq, a2->rn->flags))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exactf_negative_posix(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    char unf[2];
    int i;

    assert((a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
    assert((a2->rn->type == NPOSIXD) || (a2->rn->type == NPOSIXU) ||
	(a2->rn->type == NPOSIXA));

    seq = GET_LITERAL(a1);
    init_unfolded(unf, *seq);

    for (i = 0; i < 2; ++i)
    {
	if (_generic_isCC_A(unf[i], a2->rn->flags))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_tails(anchored, a1, a2);
}
#endif

static int compare_reg_any_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == REG_ANY);
    assert(a2->rn->type == ANYOF);

    return compare_bitmaps(anchored, a1, a2, ndot.nbitmap, 0);
}

#ifndef RC_POSIX_NODES
static int compare_digit_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    /* fprintf(stderr, "enter compare_digit_anyof\n"); */

    assert((a1->rn->type == DIGIT) || (a1->rn->type == DIGITA));
    assert(a2->rn->type == ANYOF);

    /* fprintf(stderr, "right flags = %d\n", a2->rn->flags); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NUMBER_BLOCK))
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
        U32 map;
	int cr = convert_map(a2, &map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(map & NOT_NUMBER_BLOCK))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, digit.nbitmap, 0);
}

static int compare_ndigita_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == NDIGITA);
    assert(a2->rn->type == ANYOF);

    /* from perlre: all non-ASCII characters match "\D"	*/
    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, digit.nbitmap, 0);
}
#else
static int compare_posix_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    U32 left_block;
    unsigned char *b;

    /* fprintf(stderr, "enter compare_posix_anyof\n"); */

    assert((a1->rn->type == POSIXD) || (a1->rn->type == POSIXU) ||
	(a1->rn->type == POSIXA));
    assert(a2->rn->type == ANYOF);

    if (!convert_class_narrow(a1, &left_block))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    /* fprintf(stderr, "right flags = %d\n", a2->rn->flags); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 right_map;

	/* apparently a special case... */
	if (a2->rn->flags & ANYOF_INVERT)
	{
	    return compare_mismatch(anchored, a1, a2);
	}

	int cr = convert_map(a2, &right_map);
	if (cr == -1)
	{
	    return -1;
	}

	if (!cr || !(right_map & left_block))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    if (a1->rn->flags >= SIZEOF_ARRAY(posix_regclass_bitmaps))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    b = posix_regclass_bitmaps[a1->rn->flags];
    if (!b)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, b, 0);
}

static int compare_negative_posix_anyof(int anchored, Arrow *a1, Arrow *a2)
{
    U32 left_block;
    unsigned char *b;

    /* fprintf(stderr, "enter compare_negative_posix_anyof\n"); */

    assert((a1->rn->type == NPOSIXD) || (a1->rn->type == NPOSIXU) ||
        (a1->rn->type == NPOSIXA));
    assert(a2->rn->type == ANYOF);

    if (!convert_class_narrow(a1, &left_block))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    left_block = EVERY_BLOCK & ~left_block;

    /* fprintf(stderr, "left %d -> 0x%x\n", a1->rn->flags, (unsigned)left_block); */

    if (!(a2->rn->flags & ANYOF_UNICODE_ALL))
    {
        U32 right_map;

	/* analogically with compare_posix_anyof but untested */
	if (a2->rn->flags & ANYOF_INVERT)
	{
	    return compare_mismatch(anchored, a1, a2);
	}

	int cr = convert_map(a2, &right_map);
	if (cr == -1)
	{
	    return -1;
	}

	/* fprintf(stderr, "right map = 0x%x\n", (unsigned)right_map); */

	if (!cr || !(right_map & left_block))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    if (a1->rn->flags >= SIZEOF_ARRAY(posix_regclass_bitmaps))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    b = posix_regclass_nbitmaps[a1->rn->flags];
    if (!b)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, b, 0);
}
#endif

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

    assert((a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
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

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));

    seq = GET_LITERAL(a1);

    if (!lookup[(unsigned char)(*seq)])
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_exact_multiline(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) ||
	(a1->rn->type == EXACTFU));
    assert((a2->rn->type == MBOL) || (a2->rn->type == MEOL));

    return compare_exact_byte_class(anchored, a1, a2,
        ndot.lookup);
}

#ifndef RC_POSIX_NODES
static int compare_exact_alnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == ALNUM) || (a2->rn->type == ALNUMA));

    return compare_exact_byte_class(anchored, a1, a2,
        word_bc.lookup);
}

static int compare_exact_nalnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == NALNUM) || (a2->rn->type == NALNUMA));

    return compare_exact_byte_class(anchored, a1, a2,
        word_bc.nlookup);
}

static int compare_exact_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == SPACE) || (a2->rn->type == SPACEA));

    return compare_exact_byte_class(anchored, a1, a2, whitespace.lookup);
}

static int compare_exact_nspace(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == NSPACE) || (a2->rn->type == NSPACEA));

    return compare_exact_byte_class(anchored, a1, a2, whitespace.nlookup);
}

static int compare_exact_horizontal_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == HORIZWS);

    return compare_exact_byte_class(anchored, a1, a2,
        horizontal_whitespace.lookup);
}

static int compare_exact_negative_horizontal_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NHORIZWS);

    return compare_exact_byte_class(anchored, a1, a2,
        horizontal_whitespace.nlookup);
}

static int compare_exact_vertical_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == VERTWS);

    return compare_exact_byte_class(anchored, a1, a2,
        vertical_whitespace.lookup);
}

static int compare_exact_negative_vertical_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert(a2->rn->type == NVERTWS);

    return compare_exact_byte_class(anchored, a1, a2,
        vertical_whitespace.nlookup);
}

static int compare_exact_digit(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == DIGIT) || (a2->rn->type == DIGITA));

    return compare_exact_byte_class(anchored, a1, a2, digit.lookup);
}

static int compare_exact_ndigit(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF));
    assert((a2->rn->type == NDIGIT) || (a2->rn->type == NDIGITA));

    return compare_exact_byte_class(anchored, a1, a2, digit.nlookup);
}
#endif

static int compare_anyof_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == REG_ANY);

    return compare_bitmaps(anchored, a1, a2, 0, ndot.nbitmap);
}

static int compare_exact_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
    assert(a2->rn->type == REG_ANY);

    return compare_exact_byte_class(anchored, a1, a2, ndot.nlookup);
}

#ifndef RC_POSIX_NODES
static int compare_anyof_class(int anchored, Arrow *a1, Arrow *a2,
    U32 acceptable_mask, unsigned char *required_bitmap)
{
    if (a1->rn->flags & ANYOF_UNICODE_ALL)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    if (ANYOF_NONBITMAP(a1->rn))
    {
        U32 m;

	int cr = convert_map(a1, &m);
	if (cr == -1)
	{
	    return -1;
	}

	/* fprintf(stderr, "m = 0x%x\n", (unsigned)m); */
	if (!cr || (m & ~acceptable_mask))
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }

    return compare_bitmaps(anchored, a1, a2, 0, required_bitmap);
}

static int compare_anyof_ascii_class(int anchored, Arrow *a1, Arrow *a2,
    unsigned char *required_bitmap)
{
    if (ANYOF_NONBITMAP(a1->rn))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, required_bitmap);
}

static int compare_anyof_alnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == ALNUM);

    return compare_anyof_class(anchored, a1, a2,
	ALNUM_BLOCK | ALPHA_BLOCK | NUMBER_BLOCK | UPPER_BLOCK | 
	    LOWER_BLOCK | HEX_DIGIT_BLOCK,
	word_bc.bitmap);
}

static int compare_anyof_alnuma(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == ALNUMA);

    return compare_anyof_ascii_class(anchored, a1, a2,
	word_bc.bitmap);
}

static int compare_anyof_nalnum(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == NALNUM) || (a2->rn->type == NALNUMA));

    return compare_anyof_class(anchored, a1, a2,
	SPACE_BLOCK | HORIZONTAL_SPACE_BLOCK | NOT_ALNUM_BLOCK,
	word_bc.nbitmap);
}

static int compare_anyof_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == SPACE);

    return compare_anyof_class(anchored, a1, a2,
	SPACE_BLOCK | HORIZONTAL_SPACE_BLOCK,
	whitespace.bitmap);
}

static int compare_anyof_spacea(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == SPACEA);

    return compare_anyof_ascii_class(anchored, a1, a2,
	whitespace.bitmap);
}

static int compare_anyof_nspace(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == NSPACE) || (a2->rn->type == NSPACEA));

    return compare_anyof_class(anchored, a1, a2,
	ALNUM_BLOCK | ALPHA_BLOCK | NUMBER_BLOCK | UPPER_BLOCK |
	    LOWER_BLOCK | HEX_DIGIT_BLOCK | NOT_HORIZONTAL_SPACE_BLOCK |
	    NOT_SPACE_BLOCK,
	whitespace.nbitmap);
}

static int compare_anyof_horizontal_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == HORIZWS);

    return compare_anyof_class(anchored, a1, a2,
	HORIZONTAL_SPACE_BLOCK,
	horizontal_whitespace.bitmap);
}

static int compare_anyof_negative_horizontal_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NHORIZWS);

    return compare_anyof_class(anchored, a1, a2,
	ALNUM_BLOCK | ALPHA_BLOCK | NUMBER_BLOCK | UPPER_BLOCK |
	    LOWER_BLOCK | HEX_DIGIT_BLOCK | NOT_HORIZONTAL_SPACE_BLOCK |
	    NOT_SPACE_BLOCK,
	horizontal_whitespace.nbitmap);
}

static int compare_anyof_vertical_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == VERTWS);

    return compare_anyof_class(anchored, a1, a2,
	VERTICAL_SPACE_BLOCK,
	vertical_whitespace.bitmap);
}

static int compare_anyof_negative_vertical_space(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NVERTWS);

    return compare_anyof_class(anchored, a1, a2,
	ALNUM_BLOCK | ALPHA_BLOCK | NUMBER_BLOCK | UPPER_BLOCK |
	    LOWER_BLOCK | HEX_DIGIT_BLOCK | NOT_VERTICAL_SPACE_BLOCK |
	    NOT_SPACE_BLOCK,
	vertical_whitespace.nbitmap);
}

static int compare_anyof_digit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == DIGIT);

    return compare_anyof_class(anchored, a1, a2,
	NUMBER_BLOCK,
	digit.bitmap);
}

static int compare_anyof_digita(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == DIGITA);

    return compare_anyof_ascii_class(anchored, a1, a2,
	digit.bitmap);
}

static int compare_anyof_ndigit(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == NDIGIT) || (a2->rn->type == NDIGITA));

    return compare_anyof_class(anchored, a1, a2,
	SPACE_BLOCK | HORIZONTAL_SPACE_BLOCK | VERTICAL_SPACE_BLOCK |
	NOT_ALNUM_BLOCK | NOT_NUMBER_BLOCK | NOT_HEX_DIGIT_BLOCK,
	digit.nbitmap);
}
#else
static int compare_anyof_posix(int anchored, Arrow *a1, Arrow *a2)
{
    unsigned char *b;

    /* fprintf(stderr, "enter compare_anyof_posix\n"); */

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == POSIXD);

    if (a2->rn->flags >= SIZEOF_ARRAY(posix_regclass_bitmaps))
    {
        /* fprintf(stderr, "flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    b = posix_regclass_bitmaps[a2->rn->flags];
    if (!b)
    {
        /* fprintf(stderr, "no bitmap for flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, b);
}

static int compare_anyof_posixa(int anchored, Arrow *a1, Arrow *a2)
{
    unsigned char *b;

    /* fprintf(stderr, "enter compare_anyof_posixa\n"); */

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == POSIXA);

    if (ANYOF_NONBITMAP(a1->rn))
    {
	return compare_mismatch(anchored, a1, a2);
    }

    if (a2->rn->flags >= SIZEOF_ARRAY(posix_regclass_bitmaps))
    {
        /* fprintf(stderr, "flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    b = posix_regclass_bitmaps[a2->rn->flags];
    if (!b)
    {
        /* fprintf(stderr, "no bitmap for flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, b);
}

static int compare_anyof_negative_posix(int anchored, Arrow *a1, Arrow *a2)
{
    unsigned char *b;

    /* fprintf(stderr, "enter compare_anyof_negative_posix\n"); */

    assert(a1->rn->type == ANYOF);
    assert((a2->rn->type == NPOSIXD) || (a2->rn->type == NPOSIXU) ||
        (a2->rn->type == NPOSIXA));

    if (a2->rn->flags >= SIZEOF_ARRAY(posix_regclass_nbitmaps))
    {
        /* fprintf(stderr, "flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    b = posix_regclass_nbitmaps[a2->rn->flags];
    if (!b)
    {
        /* fprintf(stderr, "no negative bitmap for flags = %d\n", a2->rn->flags); */
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_bitmaps(anchored, a1, a2, 0, b);
}

static int compare_posix_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == POSIXD) || (a1->rn->type == POSIXU) ||
	(a1->rn->type == POSIXA));
    assert(a2->rn->type == REG_ANY);

    U8 flags = a1->rn->flags;
    if (flags >= SIZEOF_ARRAY(newline_posix_regclasses))
    {
        /* fprintf(stderr, "unknown POSIX character class %d\n", flags); */
        rc_error = "unknown POSIX character class";
        return -1;
    }

    if (newline_posix_regclasses[flags])
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}

static int compare_negative_posix_reg_any(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == NPOSIXD) || (a1->rn->type == NPOSIXU) ||
        (a1->rn->type == NPOSIXA));
    assert(a2->rn->type == REG_ANY);

    U8 flags = a1->rn->flags;
    if (flags >= SIZEOF_ARRAY(newline_posix_regclasses))
    {
        rc_error = "unknown negative POSIX character class";
        return -1;
    }

    if (!newline_posix_regclasses[flags])
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_tails(anchored, a1, a2);
}
#endif

static int compare_anyof_exact(int anchored, Arrow *a1, Arrow *a2)
{
    BitFlag bf;
    char *seq;
    int i;
    unsigned char req;

    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == EXACT);

    if (a1->rn->flags & ANYOF_UNICODE_ALL)
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
    assert((a2->rn->type == EXACTF) || (a2->rn->type == EXACTFU));

    if (a1->rn->flags & ANYOF_UNICODE_ALL)
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
    assert((a2->rn->type == EXACTF) || (a2->rn->type == EXACTFU));

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

    assert((a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
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

    assert((a1->rn->type == EXACTF) || (a1->rn->type == EXACTFU));
    assert((a2->rn->type == EXACTF) || (a2->rn->type == EXACTFU));

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
    unsigned char *oktypes
#ifdef RC_POSIX_NODES
    , unsigned char *regclasses, U32 regclasses_size
#endif
    )
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
    if (t >= REGNODE_MAX)
    {
        rc_error = "Invalid node type";
        return -1;
    }
    else if (t == ANYOF)
    {
        /* fprintf(stderr, "next is bitmap; flags = 0x%x\n", left.rn->flags); */

        if (left.rn->flags & ANYOF_UNICODE_ALL)
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
    else if ((t == EXACT) || (t == EXACTF) || (t == EXACTFU))
    {
        seq = GET_LITERAL(&left);
	if (!lookup[(unsigned char)(*seq)])
	{
	    return compare_mismatch(anchored, a1, a2);
	}
    }
#ifdef RC_POSIX_NODES
    else if ((t == POSIXD) || (t == NPOSIXD))
    {
      U8 flags = left.rn->flags;
      if ((flags >= regclasses_size) || !regclasses[flags])
      {
	  return compare_mismatch(anchored, a1, a2);
      }
    }
#endif
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
    return compare_bound(anchored, a1, a2, 1, word_bc.bitmap,
        word_bc.lookup, alphanumeric_classes
#ifdef RC_POSIX_NODES
        , word_posix_regclasses, SIZEOF_ARRAY(word_posix_regclasses)
#endif
	);
}

static int compare_bol_nword(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 1, word_bc.nbitmap,
        word_bc.nlookup, non_alphanumeric_classes
#ifdef RC_POSIX_NODES
        , non_word_posix_regclasses, SIZEOF_ARRAY(non_word_posix_regclasses)
#endif
	);
}

static int compare_next_word(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 0, word_bc.bitmap,
        word_bc.lookup, alphanumeric_classes
#ifdef RC_POSIX_NODES
        , word_posix_regclasses, SIZEOF_ARRAY(word_posix_regclasses)
#endif
	);
}

static int compare_next_nword(int anchored, Arrow *a1, Arrow *a2)
{
    return compare_bound(anchored, a1, a2, 0, word_bc.nbitmap,
        word_bc.nlookup, non_alphanumeric_classes
#ifdef RC_POSIX_NODES
        , non_word_posix_regclasses, SIZEOF_ARRAY(non_word_posix_regclasses)
#endif
	);
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

    if (a1->rn->flags & ANYOF_UNICODE_ALL)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_anyof_bounds(anchored, a1, a2, word_bc.nbitmap);
}

static int compare_anyof_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    assert(a1->rn->type == ANYOF);
    assert(a2->rn->type == NBOUND);

    if (a1->rn->flags & ANYOF_UNICODE_ALL)
    {
	return compare_mismatch(anchored, a1, a2);
    }

    return compare_anyof_bounds(anchored, a1, a2, word_bc.bitmap);
}

static int compare_exact_bound(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    FCompare cmp;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) ||
	(a1->rn->type == EXACTFU));
    assert(a2->rn->type == BOUND);

    seq = GET_LITERAL(a1);

    cmp = word_bc.lookup[(unsigned char)(*seq)] ?
        compare_next_nword : compare_next_word;
    return cmp(anchored, a1, a2);
}

static int compare_exact_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    char *seq;
    FCompare cmp;

    assert((a1->rn->type == EXACT) || (a1->rn->type == EXACTF) ||
	(a1->rn->type == EXACTFU));
    assert(a2->rn->type == NBOUND);

    seq = GET_LITERAL(a1);

    cmp = word_bc.lookup[(unsigned char)(*seq)] ?
        compare_next_word : compare_next_nword;
    return cmp(anchored, a1, a2);
}

#ifdef RC_POSIX_NODES
static int compare_posix_bound(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == POSIXD) || (a1->rn->type == POSIXU) ||
	(a1->rn->type == POSIXA));
    assert(a2->rn->type == BOUND);

    U8 flags = a1->rn->flags;
    if ((flags >= SIZEOF_ARRAY(word_posix_regclasses)) ||
	(flags >= SIZEOF_ARRAY(non_word_posix_regclasses)) ||
	(!word_posix_regclasses[flags] && !non_word_posix_regclasses[flags]))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    assert(!word_posix_regclasses[flags] || !non_word_posix_regclasses[flags]);

    FCompare cmp = word_posix_regclasses[flags] ? 
        compare_next_nword : compare_next_word;
    return cmp(anchored, a1, a2);
}

static int compare_posix_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == POSIXD) || (a1->rn->type == POSIXU) ||
	(a1->rn->type == POSIXA));
    assert(a2->rn->type == NBOUND);

    U8 flags = a1->rn->flags;
    if ((flags >= SIZEOF_ARRAY(word_posix_regclasses)) ||
	(flags >= SIZEOF_ARRAY(non_word_posix_regclasses)) ||
	(!word_posix_regclasses[flags] && !non_word_posix_regclasses[flags]))
    {
        return compare_mismatch(anchored, a1, a2);
    }

    assert(!word_posix_regclasses[flags] || !non_word_posix_regclasses[flags]);

    FCompare cmp = word_posix_regclasses[flags] ? 
        compare_next_word : compare_next_nword;
    return cmp(anchored, a1, a2);
}

static int compare_negative_posix_word_bound(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == NPOSIXD) || (a1->rn->type == NPOSIXU) ||
	(a1->rn->type == NPOSIXA));
    assert(a2->rn->type == BOUND);

    /* we could accept _CC_ALPHANUMERIC as well but let's postpone it
       until we see the need */
    if (a1->rn->flags != _CC_WORDCHAR)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_next_word(anchored, a1, a2);
}

static int compare_negative_posix_word_nbound(int anchored, Arrow *a1, Arrow *a2)
{
    assert((a1->rn->type == NPOSIXD) || (a1->rn->type == NPOSIXU) ||
	(a1->rn->type == NPOSIXA));
    assert(a2->rn->type == NBOUND);

    /* we could accept _CC_ALPHANUMERIC as well but let's postpone it
       until we see the need */
    if (a1->rn->flags != _CC_WORDCHAR)
    {
        return compare_mismatch(anchored, a1, a2);
    }

    return compare_next_nword(anchored, a1, a2);
}
#endif

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

int rc_compare(REGEXP *pt1, REGEXP *pt2)
{
    Arrow a1, a2;
    regnode *p1, *p2;
#ifdef DEBUG_dump
    unsigned char *p;
    int i;    
#endif

    a1.origin = SvANY(pt1);
    a2.origin = SvANY(pt2);

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

    if ((a1->rn->type >= REGNODE_MAX) || (a2->rn->type >= REGNODE_MAX))
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
    init_byte_class(&horizontal_whitespace, horizontal_whitespace_expl,
        SIZEOF_ARRAY(horizontal_whitespace_expl));
    init_byte_class(&vertical_whitespace, vertical_whitespace_expl,
        SIZEOF_ARRAY(vertical_whitespace_expl));

    for (i = 0; i < SIZEOF_ARRAY(digit_expl); ++i)
    {
	digit_expl[i] = '0' + i;
    }

    init_byte_class(&digit, digit_expl, SIZEOF_ARRAY(digit_expl));

    memcpy(xdigit_expl, digit_expl, 10 * sizeof(char));

    wstart = 10;
    for (i = 0; i < 6; ++i)
    {
        xdigit_expl[wstart + i] = 'a' + i;
    }

    wstart += 6;
    for (i = 0; i < 6; ++i)
    {
        xdigit_expl[wstart + i] = 'A' + i;
    }

    init_byte_class(&xdigit, xdigit_expl, SIZEOF_ARRAY(xdigit_expl));

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

    init_byte_class(&word_bc, alphanumeric_expl,
        SIZEOF_ARRAY(alphanumeric_expl));
    init_byte_class(&alnum_bc, alphanumeric_expl + 1,
        SIZEOF_ARRAY(alphanumeric_expl) - 1);

    memset(alphanumeric_classes, 0, SIZEOF_ARRAY(alphanumeric_classes));
#ifndef RC_POSIX_NODES
    alphanumeric_classes[ALNUM] = alphanumeric_classes[DIGIT] = 1;
#endif

    memset(non_alphanumeric_classes, 0,
	SIZEOF_ARRAY(non_alphanumeric_classes));
#ifndef RC_POSIX_NODES
    non_alphanumeric_classes[NALNUM] = non_alphanumeric_classes[SPACE] = 
#endif
        non_alphanumeric_classes[EOS] = non_alphanumeric_classes[EOL] = 
        non_alphanumeric_classes[SEOL] = 1;

#ifdef RC_POSIX_NODES
    memset(word_posix_regclasses, 0,
        SIZEOF_ARRAY(word_posix_regclasses));
    word_posix_regclasses[_CC_WORDCHAR] = 
        word_posix_regclasses[_CC_DIGIT] = 
        word_posix_regclasses[_CC_ALPHA] = 
        word_posix_regclasses[_CC_LOWER] = 
        word_posix_regclasses[_CC_UPPER] = 
        word_posix_regclasses[_CC_UPPER] = 
        word_posix_regclasses[_CC_ALPHANUMERIC] =
        word_posix_regclasses[_CC_CASED] =
        word_posix_regclasses[_CC_XDIGIT] = 1;

    memset(non_word_posix_regclasses, 0,
        SIZEOF_ARRAY(non_word_posix_regclasses));
    non_word_posix_regclasses[_CC_PUNCT] =
        non_word_posix_regclasses[_CC_SPACE] =
        non_word_posix_regclasses[_CC_BLANK] =
        non_word_posix_regclasses[_CC_PSXSPC] =
        non_word_posix_regclasses[_CC_VERTSPACE] = 1;

    memset(newline_posix_regclasses, 0,
        SIZEOF_ARRAY(newline_posix_regclasses));
    newline_posix_regclasses[_CC_SPACE] = 
        newline_posix_regclasses[_CC_CNTRL] =
        newline_posix_regclasses[_CC_ASCII] =
        newline_posix_regclasses[_CC_VERTSPACE] = 1;
#endif

    memset(trivial_nodes, 0, SIZEOF_ARRAY(trivial_nodes));
    trivial_nodes[SUCCEED] = trivial_nodes[NOTHING] =
        trivial_nodes[TAIL] = trivial_nodes[WHILEM] = 1;

    memset(dispatch, 0, sizeof(FCompare) * REGNODE_MAX * REGNODE_MAX);

    for (i = 0; i < REGNODE_MAX; ++i)
    {
	dispatch[i][END] = success;
    }

    for (i = 0; i < REGNODE_MAX; ++i)
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][MBOL] = compare_mismatch;
    dispatch[ALNUMA][MBOL] = compare_mismatch;
    dispatch[NALNUM][MBOL] = compare_mismatch; 
    dispatch[NALNUMA][MBOL] = compare_mismatch;
    dispatch[SPACE][MBOL] = compare_mismatch;
    dispatch[SPACEA][MBOL] = compare_mismatch;
    dispatch[NSPACE][MBOL] = compare_mismatch;
    dispatch[NSPACEA][MBOL] = compare_mismatch;
    dispatch[DIGIT][MBOL] = compare_mismatch;
    dispatch[DIGITA][MBOL] = compare_mismatch;
    dispatch[NDIGIT][MBOL] = compare_mismatch;
    dispatch[NDIGITA][MBOL] = compare_mismatch;
#else
    dispatch[POSIXD][MBOL] = compare_mismatch;
    dispatch[POSIXU][MBOL] = compare_mismatch;
    dispatch[POSIXA][MBOL] = compare_mismatch;
    dispatch[NPOSIXD][MBOL] = compare_mismatch;
    dispatch[NPOSIXU][MBOL] = compare_mismatch;
    dispatch[NPOSIXA][MBOL] = compare_mismatch;
#endif
    dispatch[BRANCH][MBOL] = compare_left_branch;
    dispatch[EXACT][MBOL] = compare_exact_multiline;
    dispatch[EXACTF][MBOL] = compare_exact_multiline;
    dispatch[EXACTFU][MBOL] = compare_exact_multiline;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][MBOL] = compare_mismatch;
    dispatch[NVERTWS][MBOL] = compare_mismatch;
    dispatch[HORIZWS][MBOL] = compare_mismatch;
    dispatch[NHORIZWS][MBOL] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][MEOL] = compare_mismatch;
    dispatch[ALNUMA][MEOL] = compare_mismatch;
    dispatch[NALNUM][MEOL] = compare_mismatch;
    dispatch[NALNUMA][MEOL] = compare_mismatch;
    dispatch[SPACE][MEOL] = compare_mismatch;
    dispatch[SPACEA][MEOL] = compare_mismatch;
    dispatch[NSPACE][MEOL] = compare_mismatch;
    dispatch[NSPACEA][MEOL] = compare_mismatch;
    dispatch[DIGIT][MEOL] = compare_mismatch;
    dispatch[DIGITA][MEOL] = compare_mismatch;
    dispatch[NDIGIT][MEOL] = compare_mismatch;
    dispatch[NDIGITA][MEOL] = compare_mismatch;
#else
    dispatch[POSIXD][MEOL] = compare_mismatch;
    dispatch[POSIXU][MEOL] = compare_mismatch;
    dispatch[POSIXA][MEOL] = compare_mismatch;
    dispatch[NPOSIXD][MEOL] = compare_mismatch;
    dispatch[NPOSIXU][MEOL] = compare_mismatch;
    dispatch[NPOSIXA][MEOL] = compare_mismatch;
#endif
    dispatch[BRANCH][MEOL] = compare_left_branch;
    dispatch[EXACT][MEOL] = compare_exact_multiline;
    dispatch[EXACTF][MEOL] = compare_exact_multiline;
    dispatch[EXACTFU][MEOL] = compare_exact_multiline;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][MEOL] = compare_mismatch;
    dispatch[NVERTWS][MEOL] = compare_mismatch;
    dispatch[HORIZWS][MEOL] = compare_mismatch;
    dispatch[NHORIZWS][MEOL] = compare_mismatch;
#endif
    dispatch[OPTIMIZED][MEOL] = compare_left_tail;

    dispatch[SUCCEED][SEOL] = compare_left_tail;
    dispatch[EOS][SEOL] = compare_tails;
    dispatch[EOL][SEOL] = compare_tails;
    dispatch[SEOL][SEOL] = compare_tails;
    dispatch[BRANCH][SEOL] = compare_left_branch;
    dispatch[NOTHING][SEOL] = compare_left_tail;
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][SEOL] = compare_mismatch;
    dispatch[ALNUMA][SEOL] = compare_mismatch;
    dispatch[NALNUM][SEOL] = compare_mismatch;
    dispatch[NALNUMA][SEOL] = compare_mismatch;
    dispatch[SPACE][SEOL] = compare_mismatch;
    dispatch[SPACEA][SEOL] = compare_mismatch;
    dispatch[NSPACE][SEOL] = compare_mismatch;
    dispatch[NSPACEA][SEOL] = compare_mismatch;
    dispatch[DIGIT][SEOL] = compare_mismatch;
    dispatch[NDIGIT][SEOL] = compare_mismatch;
    dispatch[DIGITA][SEOL] = compare_mismatch;
    dispatch[NDIGITA][SEOL] = compare_mismatch;
#else
    dispatch[POSIXD][SEOL] = compare_mismatch;
    dispatch[POSIXU][SEOL] = compare_mismatch;
    dispatch[POSIXA][SEOL] = compare_mismatch;
    dispatch[NPOSIXD][SEOL] = compare_mismatch;
    dispatch[NPOSIXU][SEOL] = compare_mismatch;
    dispatch[NPOSIXA][SEOL] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][SEOL] = compare_mismatch;
    dispatch[NVERTWS][SEOL] = compare_mismatch;
    dispatch[HORIZWS][SEOL] = compare_mismatch;
    dispatch[NHORIZWS][SEOL] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][BOUND] = compare_next_nword;
    dispatch[ALNUMA][BOUND] = compare_next_nword;
    dispatch[NALNUM][BOUND] = compare_next_word;
    dispatch[NALNUMA][BOUND] = compare_next_word;
    dispatch[SPACE][BOUND] = compare_next_word;
    dispatch[SPACEA][BOUND] = compare_next_word;
    dispatch[NSPACE][BOUND] = compare_mismatch;
    dispatch[NSPACEA][BOUND] = compare_mismatch;
    dispatch[DIGIT][BOUND] = compare_next_nword;
    dispatch[DIGITA][BOUND] = compare_next_nword;
    dispatch[NDIGIT][BOUND] = compare_mismatch;
    dispatch[NDIGITA][BOUND] = compare_mismatch;
#else
    dispatch[POSIXD][BOUND] = compare_posix_bound;
    dispatch[POSIXU][BOUND] = compare_posix_bound;
    dispatch[POSIXA][BOUND] = compare_posix_bound;
    dispatch[NPOSIXD][BOUND] = compare_negative_posix_word_bound;
    dispatch[NPOSIXU][BOUND] = compare_mismatch; /* should be replaced, needs extra test */
    dispatch[NPOSIXA][BOUND] = compare_negative_posix_word_bound;
#endif
    dispatch[BRANCH][BOUND] = compare_left_branch;
    dispatch[EXACT][BOUND] = compare_exact_bound;
    dispatch[EXACTF][BOUND] = compare_exact_bound;
    dispatch[EXACTFU][BOUND] = compare_exact_bound;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][BOUND] = compare_next_word;
    dispatch[NVERTWS][BOUND] = compare_mismatch;
    dispatch[HORIZWS][BOUND] = compare_next_word;
    dispatch[NHORIZWS][BOUND] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][NBOUND] = compare_next_word;
    dispatch[ALNUMA][NBOUND] = compare_next_word;
    dispatch[NALNUM][NBOUND] = compare_next_nword;
    dispatch[NALNUMA][NBOUND] = compare_next_nword;
    dispatch[SPACE][NBOUND] = compare_next_nword;
    dispatch[SPACEA][NBOUND] = compare_next_nword;
    dispatch[NSPACE][NBOUND] = compare_mismatch;
    dispatch[NSPACEA][NBOUND] = compare_mismatch;
    dispatch[DIGIT][NBOUND] = compare_next_word;
    dispatch[DIGITA][NBOUND] = compare_next_word;
    dispatch[NDIGIT][NBOUND] = compare_mismatch;
    dispatch[NDIGITA][NBOUND] = compare_mismatch;
#else
    dispatch[POSIXD][NBOUND] = compare_posix_nbound;
    dispatch[POSIXU][NBOUND] = compare_posix_nbound;
    dispatch[POSIXA][NBOUND] = compare_posix_nbound;
    dispatch[NPOSIXD][NBOUND] = compare_negative_posix_word_nbound;
    dispatch[NPOSIXU][NBOUND] = compare_negative_posix_word_nbound;
    dispatch[NPOSIXA][NBOUND] = compare_negative_posix_word_nbound;
#endif
    dispatch[BRANCH][NBOUND] = compare_left_branch;
    dispatch[EXACT][NBOUND] = compare_exact_nbound;
    dispatch[EXACTF][NBOUND] = compare_exact_nbound;
    dispatch[EXACTFU][NBOUND] = compare_exact_nbound;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][NBOUND] = compare_next_nword;
    dispatch[NVERTWS][NBOUND] = compare_mismatch;
    dispatch[HORIZWS][NBOUND] = compare_next_nword;
    dispatch[NHORIZWS][NBOUND] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][REG_ANY] = compare_tails;
    dispatch[ALNUMA][REG_ANY] = compare_tails;
    dispatch[NALNUM][REG_ANY] = compare_mismatch;
    dispatch[NALNUMA][REG_ANY] = compare_mismatch;
    dispatch[SPACE][REG_ANY] = compare_mismatch;
    dispatch[SPACEA][REG_ANY] = compare_mismatch;
    dispatch[NSPACE][REG_ANY] = compare_tails;
    dispatch[NSPACEA][REG_ANY] = compare_tails;
    dispatch[DIGIT][REG_ANY] = compare_tails;
    dispatch[DIGITA][REG_ANY] = compare_tails;
    dispatch[NDIGIT][REG_ANY] = compare_mismatch;
    dispatch[NDIGITA][REG_ANY] = compare_mismatch;
#else
    dispatch[POSIXD][REG_ANY] = compare_posix_reg_any;
    dispatch[POSIXU][REG_ANY] = compare_posix_reg_any;
    dispatch[POSIXA][REG_ANY] = compare_posix_reg_any;
    dispatch[NPOSIXD][REG_ANY] = compare_negative_posix_reg_any;
    dispatch[NPOSIXU][REG_ANY] = compare_negative_posix_reg_any;
    dispatch[NPOSIXA][REG_ANY] = compare_negative_posix_reg_any;
#endif
    dispatch[BRANCH][REG_ANY] = compare_left_branch;
    dispatch[EXACT][REG_ANY] = compare_exact_reg_any;
    dispatch[EXACTF][REG_ANY] = compare_exact_reg_any;
    dispatch[EXACTFU][REG_ANY] = compare_exact_reg_any;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][REG_ANY] = compare_mismatch;
    dispatch[NVERTWS][REG_ANY] = compare_mismatch;
    dispatch[HORIZWS][REG_ANY] = compare_tails;
    dispatch[NHORIZWS][REG_ANY] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][SANY] = compare_tails;
    dispatch[ALNUMA][SANY] = compare_tails;
    dispatch[NALNUM][SANY] = compare_tails;
    dispatch[NALNUMA][SANY] = compare_tails;
    dispatch[SPACE][SANY] = compare_tails;
    dispatch[SPACEA][SANY] = compare_tails;
    dispatch[NSPACE][SANY] = compare_tails;
    dispatch[NSPACEA][SANY] = compare_tails;
    dispatch[DIGIT][SANY] = compare_tails;
    dispatch[DIGITA][SANY] = compare_tails;
    dispatch[NDIGIT][SANY] = compare_tails;
    dispatch[NDIGITA][SANY] = compare_tails;
#else
    dispatch[POSIXD][SANY] = compare_tails;
    dispatch[POSIXU][SANY] = compare_tails;
    dispatch[POSIXA][SANY] = compare_tails;
    dispatch[NPOSIXD][SANY] = compare_tails;
    dispatch[NPOSIXU][SANY] = compare_tails;
    dispatch[NPOSIXA][SANY] = compare_tails;
#endif
    dispatch[BRANCH][SANY] = compare_left_branch;
    dispatch[EXACT][SANY] = compare_tails;
    dispatch[EXACTF][SANY] = compare_tails;
    dispatch[EXACTFU][SANY] = compare_tails;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][SANY] = compare_tails;
    dispatch[NVERTWS][SANY] = compare_tails;
    dispatch[HORIZWS][SANY] = compare_tails;
    dispatch[NHORIZWS][SANY] = compare_tails;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][ANYOF] = compare_alnum_anyof;
    dispatch[ALNUMA][ANYOF] = compare_alnuma_anyof;
    dispatch[NALNUM][ANYOF] = compare_nalnum_anyof;
    dispatch[NALNUMA][ANYOF] = compare_nalnuma_anyof;
    dispatch[SPACE][ANYOF] = compare_space_anyof;
    dispatch[SPACEA][ANYOF] = compare_space_anyof;
    dispatch[NSPACE][ANYOF] = compare_nspace_anyof;
    dispatch[NSPACEA][ANYOF] = compare_nspacea_anyof;
    dispatch[DIGIT][ANYOF] = compare_digit_anyof;
    dispatch[DIGITA][ANYOF] = compare_digit_anyof;
    dispatch[NDIGIT][ANYOF] = compare_ndigit_anyof;
    dispatch[NDIGITA][ANYOF] = compare_ndigita_anyof;
#else
    dispatch[POSIXD][ANYOF] = compare_posix_anyof;
    dispatch[POSIXU][ANYOF] = compare_posix_anyof;
    dispatch[POSIXA][ANYOF] = compare_posix_anyof;
    dispatch[NPOSIXD][ANYOF] = compare_negative_posix_anyof;
    dispatch[NPOSIXU][ANYOF] = compare_negative_posix_anyof;
    dispatch[NPOSIXA][ANYOF] = compare_negative_posix_anyof;
#endif
    dispatch[BRANCH][ANYOF] = compare_left_branch;
    dispatch[EXACT][ANYOF] = compare_exact_anyof;
    dispatch[EXACTF][ANYOF] = compare_exactf_anyof;
    dispatch[EXACTFU][ANYOF] = compare_exactf_anyof;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][ANYOF] = compare_vertical_space_anyof;
    dispatch[NVERTWS][ANYOF] = compare_negative_vertical_space_anyof;
    dispatch[HORIZWS][ANYOF] = compare_horizontal_space_anyof;
    dispatch[NHORIZWS][ANYOF] = compare_negative_horizontal_space_anyof;
#endif
    dispatch[OPTIMIZED][ANYOF] = compare_left_tail;

#ifndef RC_POSIX_NODES
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
    dispatch[ALNUMA][ALNUM] = compare_tails;
    dispatch[NALNUM][ALNUM] = compare_mismatch;
    dispatch[NALNUMA][ALNUM] = compare_mismatch;
    dispatch[SPACE][ALNUM] = compare_mismatch;
    dispatch[SPACEA][ALNUM] = compare_mismatch;
    dispatch[NSPACE][ALNUM] = compare_mismatch;
    dispatch[NSPACEA][ALNUM] = compare_mismatch;
    dispatch[DIGIT][ALNUM] = compare_tails;
    dispatch[DIGITA][ALNUM] = compare_tails;
    dispatch[NDIGIT][ALNUM] = compare_mismatch;
    dispatch[NDIGITA][ALNUM] = compare_mismatch;
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
    dispatch[VERTWS][ALNUM] = compare_mismatch;
    dispatch[NVERTWS][ALNUM] = compare_mismatch;
    dispatch[HORIZWS][ALNUM] = compare_mismatch;
    dispatch[NHORIZWS][ALNUM] = compare_mismatch;
    dispatch[OPTIMIZED][ALNUM] = compare_left_tail;

    dispatch[SUCCEED][ALNUMA] = compare_left_tail;
    dispatch[BOL][ALNUMA] = compare_bol;
    dispatch[MBOL][ALNUMA] = compare_bol;
    dispatch[SBOL][ALNUMA] = compare_bol;
    dispatch[BOUND][ALNUMA] = compare_mismatch;
    dispatch[NBOUND][ALNUMA] = compare_mismatch;
    dispatch[REG_ANY][ALNUMA] = compare_mismatch;
    dispatch[SANY][ALNUMA] = compare_mismatch;
    dispatch[ANYOF][ALNUMA] = compare_anyof_alnuma;
    dispatch[ALNUM][ALNUMA] = compare_mismatch;
    dispatch[ALNUMA][ALNUMA] = compare_tails;
    dispatch[NALNUM][ALNUMA] = compare_mismatch;
    dispatch[NALNUMA][ALNUMA] = compare_mismatch;
    dispatch[SPACE][ALNUMA] = compare_mismatch;
    dispatch[SPACEA][ALNUMA] = compare_mismatch;
    dispatch[NSPACE][ALNUMA] = compare_mismatch;
    dispatch[NSPACEA][ALNUMA] = compare_mismatch;
    dispatch[DIGIT][ALNUMA] = compare_mismatch;
    dispatch[DIGITA][ALNUMA] = compare_tails;
    dispatch[NDIGIT][ALNUMA] = compare_mismatch;
    dispatch[NDIGITA][ALNUMA] = compare_mismatch;
    dispatch[BRANCH][ALNUMA] = compare_left_branch;
    dispatch[EXACT][ALNUMA] = compare_exact_alnum;
    dispatch[EXACTF][ALNUMA] = compare_exact_alnum;
    dispatch[NOTHING][ALNUMA] = compare_left_tail;
    dispatch[TAIL][ALNUMA] = compare_left_tail;
    dispatch[STAR][ALNUMA] = compare_mismatch;
    dispatch[PLUS][ALNUMA] = compare_left_plus;
    dispatch[CURLY][ALNUMA] = compare_left_curly;
    dispatch[CURLYM][ALNUMA] = compare_left_curly;
    dispatch[CURLYX][ALNUMA] = compare_left_curly;
    dispatch[WHILEM][ALNUMA] = compare_left_tail;
    dispatch[OPEN][ALNUMA] = compare_left_open;
    dispatch[CLOSE][ALNUMA] = compare_left_tail;
    dispatch[IFMATCH][ALNUMA] = compare_after_assertion;
    dispatch[UNLESSM][ALNUMA] = compare_after_assertion;
    dispatch[MINMOD][ALNUMA] = compare_left_tail;
    dispatch[VERTWS][ALNUMA] = compare_mismatch;
    dispatch[NVERTWS][ALNUMA] = compare_mismatch;
    dispatch[HORIZWS][ALNUMA] = compare_mismatch;
    dispatch[NHORIZWS][ALNUMA] = compare_mismatch;
    dispatch[OPTIMIZED][ALNUMA] = compare_left_tail;

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
    dispatch[ALNUMA][NALNUM] = compare_mismatch;
    dispatch[NALNUM][NALNUM] = compare_tails;
    dispatch[NALNUMA][NALNUM] = compare_mismatch;
    dispatch[SPACE][NALNUM] = compare_tails;
    dispatch[SPACEA][NALNUM] = compare_tails;
    dispatch[NSPACE][NALNUM] = compare_mismatch;
    dispatch[NSPACEA][NALNUM] = compare_mismatch;
    dispatch[DIGIT][NALNUM] = compare_mismatch;
    dispatch[DIGITA][NALNUM] = compare_mismatch;
    dispatch[NDIGIT][NALNUM] = compare_mismatch;
    dispatch[NDIGITA][NALNUM] = compare_mismatch;
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
    dispatch[VERTWS][NALNUM] = compare_tails;
    dispatch[NVERTWS][NALNUM] = compare_mismatch;
    dispatch[HORIZWS][NALNUM] = compare_tails;
    dispatch[NHORIZWS][NALNUM] = compare_mismatch;
    dispatch[OPTIMIZED][NALNUM] = compare_left_tail;

    dispatch[SUCCEED][NALNUMA] = compare_left_tail;
    dispatch[BOL][NALNUMA] = compare_bol;
    dispatch[MBOL][NALNUMA] = compare_bol;
    dispatch[SBOL][NALNUMA] = compare_bol;
    dispatch[BOUND][NALNUMA] = compare_mismatch;
    dispatch[NBOUND][NALNUMA] = compare_mismatch;
    dispatch[REG_ANY][NALNUMA] = compare_mismatch;
    dispatch[SANY][NALNUMA] = compare_mismatch;
    dispatch[ANYOF][NALNUMA] = compare_anyof_nalnum;
    dispatch[ALNUM][NALNUMA] = compare_mismatch;
    dispatch[ALNUMA][NALNUMA] = compare_mismatch;
    dispatch[NALNUM][NALNUMA] = compare_tails;
    dispatch[NALNUMA][NALNUMA] = compare_tails;
    dispatch[SPACE][NALNUMA] = compare_tails;
    dispatch[SPACEA][NALNUMA] = compare_tails;
    dispatch[NSPACE][NALNUMA] = compare_mismatch;
    dispatch[NSPACEA][NALNUMA] = compare_mismatch;
    dispatch[DIGIT][NALNUMA] = compare_mismatch;
    dispatch[DIGITA][NALNUMA] = compare_mismatch;
    dispatch[NDIGIT][NALNUMA] = compare_mismatch;
    dispatch[NDIGITA][NALNUMA] = compare_mismatch;
    dispatch[BRANCH][NALNUMA] = compare_left_branch;
    dispatch[EXACT][NALNUMA] = compare_exact_nalnum;
    dispatch[EXACTF][NALNUMA] = compare_exact_nalnum;
    dispatch[NOTHING][NALNUMA] = compare_left_tail;
    dispatch[TAIL][NALNUMA] = compare_left_tail;
    dispatch[STAR][NALNUMA] = compare_mismatch;
    dispatch[PLUS][NALNUMA] = compare_left_plus;
    dispatch[CURLY][NALNUMA] = compare_left_curly;
    dispatch[CURLYM][NALNUMA] = compare_left_curly;
    dispatch[CURLYX][NALNUMA] = compare_left_curly;
    dispatch[WHILEM][NALNUMA] = compare_left_tail;
    dispatch[OPEN][NALNUMA] = compare_left_open;
    dispatch[CLOSE][NALNUMA] = compare_left_tail;
    dispatch[IFMATCH][NALNUMA] = compare_after_assertion;
    dispatch[UNLESSM][NALNUMA] = compare_after_assertion;
    dispatch[MINMOD][NALNUMA] = compare_left_tail;
    dispatch[VERTWS][NALNUMA] = compare_tails;
    dispatch[NVERTWS][NALNUMA] = compare_mismatch;
    dispatch[HORIZWS][NALNUMA] = compare_tails;
    dispatch[NHORIZWS][NALNUMA] = compare_mismatch;
    dispatch[OPTIMIZED][NALNUMA] = compare_left_tail;

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
    dispatch[ALNUMA][SPACE] = compare_mismatch;
    dispatch[NALNUM][SPACE] = compare_mismatch;
    dispatch[NALNUMA][SPACE] = compare_mismatch;
    dispatch[SPACE][SPACE] = compare_tails;
    dispatch[SPACEA][SPACE] = compare_tails;
    dispatch[NSPACE][SPACE] = compare_mismatch;
    dispatch[NSPACEA][SPACE] = compare_mismatch;
    dispatch[DIGIT][SPACE] = compare_mismatch;
    dispatch[DIGITA][SPACE] = compare_mismatch;
    dispatch[NDIGIT][SPACE] = compare_mismatch;
    dispatch[NDIGITA][SPACE] = compare_mismatch;
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
    dispatch[VERTWS][SPACE] = compare_mismatch;
    dispatch[NVERTWS][SPACE] = compare_mismatch;
    dispatch[HORIZWS][SPACE] = compare_tails;
    dispatch[NHORIZWS][SPACE] = compare_mismatch;
    dispatch[OPTIMIZED][SPACE] = compare_left_tail;

    dispatch[SUCCEED][SPACEA] = compare_left_tail;
    dispatch[BOL][SPACEA] = compare_bol;
    dispatch[MBOL][SPACEA] = compare_bol;
    dispatch[SBOL][SPACEA] = compare_bol;
    dispatch[BOUND][SPACEA] = compare_mismatch;
    dispatch[NBOUND][SPACEA] = compare_mismatch;
    dispatch[REG_ANY][SPACEA] = compare_mismatch;
    dispatch[SANY][SPACEA] = compare_mismatch;
    dispatch[ANYOF][SPACEA] = compare_anyof_spacea;
    dispatch[ALNUM][SPACEA] = compare_mismatch;
    dispatch[ALNUMA][SPACEA] = compare_mismatch;
    dispatch[NALNUM][SPACEA] = compare_mismatch;
    dispatch[NALNUMA][SPACEA] = compare_mismatch;
    dispatch[SPACE][SPACEA] = compare_mismatch;
    dispatch[SPACEA][SPACEA] = compare_tails;
    dispatch[NSPACE][SPACEA] = compare_mismatch;
    dispatch[NSPACEA][SPACEA] = compare_mismatch;
    dispatch[DIGIT][SPACEA] = compare_mismatch;
    dispatch[DIGITA][SPACEA] = compare_mismatch;
    dispatch[NDIGIT][SPACEA] = compare_mismatch;
    dispatch[NDIGITA][SPACEA] = compare_mismatch;
    dispatch[BRANCH][SPACEA] = compare_left_branch;
    dispatch[EXACT][SPACEA] = compare_exact_space;
    dispatch[EXACTF][SPACEA] = compare_exact_space;
    dispatch[NOTHING][SPACEA] = compare_left_tail;
    dispatch[TAIL][SPACEA] = compare_left_tail;
    dispatch[STAR][SPACEA] = compare_mismatch;
    dispatch[PLUS][SPACEA] = compare_left_plus;
    dispatch[CURLY][SPACEA] = compare_left_curly;
    dispatch[CURLYM][SPACEA] = compare_left_curly;
    dispatch[CURLYX][SPACEA] = compare_left_curly;
    dispatch[WHILEM][SPACEA] = compare_left_tail;
    dispatch[OPEN][SPACEA] = compare_left_open;
    dispatch[CLOSE][SPACEA] = compare_left_tail;
    dispatch[IFMATCH][SPACEA] = compare_after_assertion;
    dispatch[UNLESSM][SPACEA] = compare_after_assertion;
    dispatch[MINMOD][SPACEA] = compare_left_tail;
    dispatch[VERTWS][SPACEA] = compare_mismatch;
    dispatch[NVERTWS][SPACEA] = compare_mismatch;
    dispatch[HORIZWS][SPACEA] = compare_mismatch;
    dispatch[NHORIZWS][SPACEA] = compare_mismatch;
    dispatch[OPTIMIZED][SPACEA] = compare_left_tail;

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
    dispatch[ALNUMA][NSPACE] = compare_tails;
    dispatch[NALNUM][NSPACE] = compare_mismatch;
    dispatch[NALNUMA][NSPACE] = compare_mismatch;
    dispatch[SPACE][NSPACE] = compare_mismatch;
    dispatch[SPACEA][NSPACE] = compare_mismatch;
    dispatch[NSPACE][NSPACE] = compare_tails;
    dispatch[NSPACEA][NSPACE] = compare_tails;
    dispatch[DIGIT][NSPACE] = compare_tails;
    dispatch[DIGITA][NSPACE] = compare_tails;
    dispatch[NDIGIT][NSPACE] = compare_mismatch;
    dispatch[NDIGITA][NSPACE] = compare_mismatch;
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
    dispatch[VERTWS][NSPACE] = compare_mismatch;
    dispatch[NVERTWS][NSPACE] = compare_mismatch;
    dispatch[HORIZWS][NSPACE] = compare_mismatch;
    dispatch[NHORIZWS][NSPACE] = compare_mismatch;
    dispatch[OPTIMIZED][NSPACE] = compare_left_tail;

    dispatch[SUCCEED][NSPACEA] = compare_left_tail;
    dispatch[BOL][NSPACEA] = compare_bol;
    dispatch[MBOL][NSPACEA] = compare_bol;
    dispatch[SBOL][NSPACEA] = compare_bol;
    dispatch[BOUND][NSPACEA] = compare_mismatch;
    dispatch[NBOUND][NSPACEA] = compare_mismatch;
    dispatch[REG_ANY][NSPACEA] = compare_mismatch;
    dispatch[SANY][NSPACEA] = compare_mismatch;
    dispatch[ANYOF][NSPACEA] = compare_anyof_nspace;
    dispatch[ALNUM][NSPACEA] = compare_mismatch;
    dispatch[ALNUMA][NSPACEA] = compare_tails;
    dispatch[NALNUM][NSPACEA] = compare_mismatch;
    dispatch[NALNUMA][NSPACEA] = compare_mismatch;
    dispatch[SPACE][NSPACEA] = compare_mismatch;
    dispatch[SPACEA][NSPACEA] = compare_mismatch;
    dispatch[NSPACE][NSPACEA] = compare_mismatch;
    dispatch[NSPACEA][NSPACEA] = compare_tails;
    dispatch[DIGIT][NSPACEA] = compare_mismatch;
    dispatch[DIGITA][NSPACEA] = compare_tails;
    dispatch[NDIGIT][NSPACEA] = compare_mismatch;
    dispatch[NDIGITA][NSPACEA] = compare_mismatch;
    dispatch[BRANCH][NSPACEA] = compare_left_branch;
    dispatch[EXACT][NSPACEA] = compare_exact_nspace;
    dispatch[EXACTF][NSPACEA] = compare_exact_nspace;
    dispatch[NOTHING][NSPACEA] = compare_left_tail;
    dispatch[TAIL][NSPACEA] = compare_left_tail;
    dispatch[STAR][NSPACEA] = compare_mismatch;
    dispatch[PLUS][NSPACEA] = compare_left_plus;
    dispatch[CURLY][NSPACEA] = compare_left_curly;
    dispatch[CURLYM][NSPACEA] = compare_left_curly;
    dispatch[CURLYX][NSPACEA] = compare_left_curly;
    dispatch[WHILEM][NSPACEA] = compare_left_tail;
    dispatch[OPEN][NSPACEA] = compare_left_open;
    dispatch[CLOSE][NSPACEA] = compare_left_tail;
    dispatch[IFMATCH][NSPACEA] = compare_after_assertion;
    dispatch[UNLESSM][NSPACEA] = compare_after_assertion;
    dispatch[MINMOD][NSPACEA] = compare_left_tail;
    dispatch[VERTWS][NSPACEA] = compare_mismatch;
    dispatch[NVERTWS][NSPACEA] = compare_mismatch;
    dispatch[HORIZWS][NSPACEA] = compare_mismatch;
    dispatch[NHORIZWS][NSPACEA] = compare_mismatch;
    dispatch[OPTIMIZED][NSPACEA] = compare_left_tail;

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
    dispatch[ALNUMA][DIGIT] = compare_mismatch;
    dispatch[NALNUM][DIGIT] = compare_mismatch;
    dispatch[NALNUMA][DIGIT] = compare_mismatch;
    dispatch[SPACE][DIGIT] = compare_mismatch;
    dispatch[SPACEA][DIGIT] = compare_mismatch;
    dispatch[NSPACE][DIGIT] = compare_mismatch;
    dispatch[NSPACEA][DIGIT] = compare_mismatch;
    dispatch[DIGIT][DIGIT] = compare_tails;
    dispatch[DIGITA][DIGIT] = compare_tails;
    dispatch[NDIGIT][DIGIT] = compare_mismatch;
    dispatch[NDIGITA][DIGIT] = compare_mismatch;
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
    dispatch[VERTWS][DIGIT] = compare_mismatch;
    dispatch[NVERTWS][DIGIT] = compare_mismatch;
    dispatch[HORIZWS][DIGIT] = compare_mismatch;
    dispatch[NHORIZWS][DIGIT] = compare_mismatch;
    dispatch[OPTIMIZED][DIGIT] = compare_left_tail;

    dispatch[SUCCEED][DIGITA] = compare_left_tail;
    dispatch[BOL][DIGITA] = compare_bol;
    dispatch[MBOL][DIGITA] = compare_bol;
    dispatch[SBOL][DIGITA] = compare_bol;
    dispatch[BOUND][DIGITA] = compare_mismatch;
    dispatch[NBOUND][DIGITA] = compare_mismatch;
    dispatch[REG_ANY][DIGITA] = compare_mismatch;
    dispatch[SANY][DIGITA] = compare_mismatch;
    dispatch[ANYOF][DIGITA] = compare_anyof_digita;
    dispatch[ALNUM][DIGITA] = compare_mismatch;
    dispatch[ALNUMA][DIGITA] = compare_mismatch;
    dispatch[NALNUM][DIGITA] = compare_mismatch;
    dispatch[NALNUMA][DIGITA] = compare_mismatch;
    dispatch[SPACE][DIGITA] = compare_mismatch;
    dispatch[SPACEA][DIGITA] = compare_mismatch;
    dispatch[NSPACE][DIGITA] = compare_mismatch;
    dispatch[NSPACEA][DIGITA] = compare_mismatch;
    dispatch[DIGIT][DIGITA] = compare_mismatch;
    dispatch[DIGITA][DIGITA] = compare_tails;
    dispatch[NDIGIT][DIGITA] = compare_mismatch;
    dispatch[NDIGITA][DIGITA] = compare_mismatch;
    dispatch[BRANCH][DIGITA] = compare_left_branch;
    dispatch[EXACT][DIGITA] = compare_exact_digit;
    dispatch[EXACTF][DIGITA] = compare_exact_digit;
    dispatch[NOTHING][DIGITA] = compare_left_tail;
    dispatch[TAIL][DIGITA] = compare_left_tail;
    dispatch[STAR][DIGITA] = compare_mismatch;
    dispatch[PLUS][DIGITA] = compare_left_plus;
    dispatch[CURLY][DIGITA] = compare_left_curly;
    dispatch[CURLYM][DIGITA] = compare_left_curly;
    dispatch[CURLYX][DIGITA] = compare_left_curly;
    dispatch[WHILEM][DIGITA] = compare_left_tail;
    dispatch[OPEN][DIGITA] = compare_left_open;
    dispatch[CLOSE][DIGITA] = compare_left_tail;
    dispatch[IFMATCH][DIGITA] = compare_after_assertion;
    dispatch[UNLESSM][DIGITA] = compare_after_assertion;
    dispatch[MINMOD][DIGITA] = compare_left_tail;
    dispatch[VERTWS][DIGITA] = compare_mismatch;
    dispatch[NVERTWS][DIGITA] = compare_mismatch;
    dispatch[HORIZWS][DIGITA] = compare_mismatch;
    dispatch[NHORIZWS][DIGITA] = compare_mismatch;
    dispatch[OPTIMIZED][DIGITA] = compare_left_tail;

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
    dispatch[ALNUMA][NDIGIT] = compare_mismatch;
    dispatch[NALNUM][NDIGIT] = compare_tails;
    dispatch[NALNUMA][NDIGIT] = compare_mismatch;
    dispatch[SPACE][NDIGIT] = compare_tails;
    dispatch[SPACEA][NDIGIT] = compare_tails;
    dispatch[NSPACE][NDIGIT] = compare_mismatch;
    dispatch[NSPACEA][NDIGIT] = compare_mismatch;
    dispatch[DIGIT][NDIGIT] = compare_mismatch;
    dispatch[DIGITA][NDIGIT] = compare_mismatch;
    dispatch[NDIGIT][NDIGIT] = compare_tails;
    dispatch[NDIGITA][NDIGIT] = compare_mismatch;
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
    dispatch[VERTWS][NDIGIT] = compare_tails;
    dispatch[NVERTWS][NDIGIT] = compare_mismatch;
    dispatch[HORIZWS][NDIGIT] = compare_tails;
    dispatch[NHORIZWS][NDIGIT] = compare_mismatch;
    dispatch[OPTIMIZED][NDIGIT] = compare_left_tail;

    dispatch[SUCCEED][NDIGITA] = compare_left_tail;
    dispatch[BOL][NDIGITA] = compare_bol;
    dispatch[MBOL][NDIGITA] = compare_bol;
    dispatch[SBOL][NDIGITA] = compare_bol;
    dispatch[BOUND][NDIGITA] = compare_mismatch;
    dispatch[NBOUND][NDIGITA] = compare_mismatch;
    dispatch[REG_ANY][NDIGITA] = compare_mismatch;
    dispatch[SANY][NDIGITA] = compare_mismatch;
    dispatch[ANYOF][NDIGITA] = compare_anyof_ndigit;
    dispatch[ALNUM][NDIGITA] = compare_mismatch;
    dispatch[ALNUMA][NDIGITA] = compare_mismatch;
    dispatch[NALNUM][NDIGITA] = compare_mismatch; /* conservative */
    dispatch[NALNUMA][NDIGITA] = compare_tails;
    dispatch[SPACE][NDIGITA] = compare_tails;
    dispatch[SPACEA][NDIGITA] = compare_tails;
    dispatch[NSPACE][NDIGITA] = compare_mismatch;
    dispatch[NSPACEA][NDIGITA] = compare_mismatch;
    dispatch[DIGIT][NDIGITA] = compare_mismatch;
    dispatch[DIGITA][NDIGITA] = compare_mismatch;
    dispatch[NDIGIT][NDIGITA] = compare_mismatch;
    dispatch[NDIGITA][NDIGITA] = compare_tails;
    dispatch[BRANCH][NDIGITA] = compare_left_branch;
    dispatch[EXACT][NDIGITA] = compare_exact_ndigit;
    dispatch[EXACTF][NDIGITA] = compare_exact_ndigit;
    dispatch[NOTHING][NDIGITA] = compare_left_tail;
    dispatch[TAIL][NDIGITA] = compare_left_tail;
    dispatch[STAR][NDIGITA] = compare_mismatch;
    dispatch[PLUS][NDIGITA] = compare_left_plus;
    dispatch[CURLY][NDIGITA] = compare_left_curly;
    dispatch[CURLYM][NDIGITA] = compare_left_curly;
    dispatch[CURLYX][NDIGITA] = compare_left_curly;
    dispatch[WHILEM][NDIGITA] = compare_left_tail;
    dispatch[OPEN][NDIGITA] = compare_left_open;
    dispatch[CLOSE][NDIGITA] = compare_left_tail;
    dispatch[IFMATCH][NDIGITA] = compare_after_assertion;
    dispatch[UNLESSM][NDIGITA] = compare_after_assertion;
    dispatch[MINMOD][NDIGITA] = compare_left_tail;
    dispatch[VERTWS][NDIGITA] = compare_tails;
    dispatch[NVERTWS][NDIGITA] = compare_mismatch;
    dispatch[HORIZWS][NDIGITA] = compare_tails;
    dispatch[NHORIZWS][NDIGITA] = compare_mismatch;
    dispatch[OPTIMIZED][NDIGITA] = compare_left_tail;
#else
    dispatch[SUCCEED][POSIXD] = compare_left_tail;
    dispatch[BOL][POSIXD] = compare_bol;
    dispatch[MBOL][POSIXD] = compare_bol;
    dispatch[SBOL][POSIXD] = compare_bol;
    dispatch[BOUND][POSIXD] = compare_mismatch;
    dispatch[NBOUND][POSIXD] = compare_mismatch;
    dispatch[REG_ANY][POSIXD] = compare_mismatch;
    dispatch[SANY][POSIXD] = compare_mismatch;
    dispatch[ANYOF][POSIXD] = compare_anyof_posix;
    dispatch[POSIXD][POSIXD] = compare_posix_posix;
    dispatch[POSIXU][POSIXD] = compare_posix_posix;
    dispatch[POSIXA][POSIXD] = compare_posix_posix;
    dispatch[NPOSIXD][POSIXD] = compare_mismatch;
    dispatch[NPOSIXU][POSIXD] = compare_mismatch;
    dispatch[NPOSIXA][POSIXD] = compare_mismatch;
    dispatch[BRANCH][POSIXD] = compare_left_branch;
    dispatch[EXACT][POSIXD] = compare_exact_posix;
    dispatch[EXACTF][POSIXD] = compare_exactf_posix;
    dispatch[EXACTFU][POSIXD] = compare_exactf_posix;
    dispatch[NOTHING][POSIXD] = compare_left_tail;
    dispatch[STAR][POSIXD] = compare_mismatch;
    dispatch[PLUS][POSIXD] = compare_left_plus;
    dispatch[CURLY][POSIXD] = compare_left_curly;
    dispatch[CURLYM][POSIXD] = compare_left_curly;
    dispatch[CURLYX][POSIXD] = compare_left_curly;
    dispatch[OPEN][POSIXD] = compare_left_open;
    dispatch[CLOSE][POSIXD] = compare_left_tail;
    dispatch[IFMATCH][POSIXD] = compare_after_assertion;
    dispatch[UNLESSM][POSIXD] = compare_after_assertion;
    dispatch[MINMOD][POSIXD] = compare_left_tail;
    dispatch[OPTIMIZED][POSIXD] = compare_left_tail;

    dispatch[SUCCEED][POSIXU] = compare_left_tail;
    dispatch[BOL][POSIXU] = compare_bol;
    dispatch[MBOL][POSIXU] = compare_bol;
    dispatch[SBOL][POSIXU] = compare_bol;
    dispatch[BOUND][POSIXU] = compare_mismatch;
    dispatch[NBOUND][POSIXU] = compare_mismatch;
    dispatch[REG_ANY][POSIXU] = compare_mismatch;
    dispatch[SANY][POSIXU] = compare_mismatch;
    dispatch[POSIXD][POSIXU] = compare_posix_posix;
    dispatch[POSIXA][POSIXU] = compare_mismatch;
    dispatch[POSIXU][POSIXU] = compare_posix_posix;
    dispatch[NPOSIXD][POSIXU] = compare_mismatch;
    dispatch[NPOSIXU][POSIXU] = compare_mismatch;
    dispatch[NPOSIXA][POSIXU] = compare_mismatch;
    dispatch[BRANCH][POSIXU] = compare_left_branch;
    dispatch[EXACT][POSIXU] = compare_exact_posix;
    dispatch[EXACTF][POSIXU] = compare_exact_posix;
    dispatch[EXACTFU][POSIXU] = compare_exact_posix;
    dispatch[NOTHING][POSIXU] = compare_left_tail;
    dispatch[STAR][POSIXU] = compare_mismatch;
    dispatch[PLUS][POSIXU] = compare_left_plus;
    dispatch[CURLY][POSIXU] = compare_left_curly;
    dispatch[CURLYM][POSIXU] = compare_left_curly;
    dispatch[CURLYX][POSIXU] = compare_left_curly;
    dispatch[OPEN][POSIXU] = compare_left_open;
    dispatch[CLOSE][POSIXU] = compare_left_tail;
    dispatch[IFMATCH][POSIXU] = compare_after_assertion;
    dispatch[UNLESSM][POSIXU] = compare_after_assertion;
    dispatch[MINMOD][POSIXU] = compare_left_tail;
    dispatch[OPTIMIZED][POSIXU] = compare_left_tail;

    dispatch[SUCCEED][POSIXA] = compare_left_tail;
    dispatch[BOL][POSIXA] = compare_bol;
    dispatch[MBOL][POSIXA] = compare_bol;
    dispatch[SBOL][POSIXA] = compare_bol;
    dispatch[BOUND][POSIXA] = compare_mismatch;
    dispatch[NBOUND][POSIXA] = compare_mismatch;
    dispatch[REG_ANY][POSIXA] = compare_mismatch;
    dispatch[SANY][POSIXA] = compare_mismatch;
    dispatch[ANYOF][POSIXA] = compare_anyof_posixa;
    dispatch[POSIXD][POSIXA] = compare_mismatch;
    dispatch[POSIXU][POSIXA] = compare_mismatch;
    dispatch[POSIXA][POSIXA] = compare_posix_posix;
    dispatch[NPOSIXD][POSIXA] = compare_mismatch;
    dispatch[NPOSIXU][POSIXA] = compare_mismatch;
    dispatch[NPOSIXA][POSIXA] = compare_mismatch;
    dispatch[BRANCH][POSIXA] = compare_left_branch;
    dispatch[EXACT][POSIXA] = compare_exact_posix;
    dispatch[EXACTF][POSIXA] = compare_exact_posix;
    dispatch[EXACTFU][POSIXA] = compare_exact_posix;
    dispatch[NOTHING][POSIXA] = compare_left_tail;
    dispatch[STAR][POSIXA] = compare_mismatch;
    dispatch[PLUS][POSIXA] = compare_left_plus;
    dispatch[CURLY][POSIXA] = compare_left_curly;
    dispatch[CURLYM][POSIXA] = compare_left_curly;
    dispatch[CURLYX][POSIXA] = compare_left_curly;
    dispatch[OPEN][POSIXA] = compare_left_open;
    dispatch[CLOSE][POSIXA] = compare_left_tail;
    dispatch[IFMATCH][POSIXA] = compare_after_assertion;
    dispatch[UNLESSM][POSIXA] = compare_after_assertion;
    dispatch[MINMOD][POSIXA] = compare_left_tail;
    dispatch[OPTIMIZED][POSIXA] = compare_left_tail;

    dispatch[SUCCEED][NPOSIXD] = compare_left_tail;
    dispatch[BOL][NPOSIXD] = compare_bol;
    dispatch[MBOL][NPOSIXD] = compare_bol;
    dispatch[SBOL][NPOSIXD] = compare_bol;
    dispatch[BOUND][NPOSIXD] = compare_mismatch;
    dispatch[NBOUND][NPOSIXD] = compare_mismatch;
    dispatch[REG_ANY][NPOSIXD] = compare_mismatch;
    dispatch[SANY][NPOSIXD] = compare_mismatch;
    dispatch[ANYOF][NPOSIXD] = compare_anyof_negative_posix;
    dispatch[POSIXD][NPOSIXD] = compare_posix_negative_posix;
    dispatch[POSIXU][NPOSIXD] = compare_posix_negative_posix;
    dispatch[POSIXA][NPOSIXD] = compare_posix_negative_posix;
    dispatch[NPOSIXD][NPOSIXD] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXU][NPOSIXD] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXA][NPOSIXD] = compare_mismatch;
    dispatch[BRANCH][NPOSIXD] = compare_left_branch;
    dispatch[EXACT][NPOSIXD] = compare_exact_negative_posix;
    dispatch[EXACTF][NPOSIXD] = compare_exactf_negative_posix;
    dispatch[EXACTFU][NPOSIXD] = compare_exactf_negative_posix;
    dispatch[NOTHING][NPOSIXD] = compare_left_tail;
    dispatch[STAR][NPOSIXD] = compare_mismatch;
    dispatch[PLUS][NPOSIXD] = compare_left_plus;
    dispatch[CURLY][NPOSIXD] = compare_left_curly;
    dispatch[CURLYM][NPOSIXD] = compare_left_curly;
    dispatch[CURLYX][NPOSIXD] = compare_left_curly;
    dispatch[OPEN][NPOSIXD] = compare_left_open;
    dispatch[CLOSE][NPOSIXD] = compare_left_tail;
    dispatch[IFMATCH][NPOSIXD] = compare_after_assertion;
    dispatch[UNLESSM][NPOSIXD] = compare_after_assertion;
    dispatch[MINMOD][NPOSIXD] = compare_left_tail;
    dispatch[OPTIMIZED][NPOSIXD] = compare_left_tail;

    dispatch[SUCCEED][NPOSIXU] = compare_left_tail;
    dispatch[BOL][NPOSIXU] = compare_bol;
    dispatch[MBOL][NPOSIXU] = compare_bol;
    dispatch[SBOL][NPOSIXU] = compare_bol;
    dispatch[BOUND][NPOSIXU] = compare_mismatch;
    dispatch[NBOUND][NPOSIXU] = compare_mismatch;
    dispatch[REG_ANY][NPOSIXU] = compare_mismatch;
    dispatch[SANY][NPOSIXU] = compare_mismatch;
    dispatch[ANYOF][NPOSIXU] = compare_anyof_negative_posix;
    dispatch[POSIXD][NPOSIXU] = compare_posix_negative_posix;
    dispatch[POSIXU][NPOSIXU] = compare_posix_negative_posix;
    dispatch[POSIXA][NPOSIXU] = compare_posix_negative_posix;
    dispatch[NPOSIXD][NPOSIXU] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXU][NPOSIXU] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXA][NPOSIXU] = compare_mismatch;
    dispatch[BRANCH][NPOSIXU] = compare_left_branch;
    dispatch[EXACT][NPOSIXU] = compare_exact_negative_posix;
    dispatch[EXACTF][NPOSIXU] = compare_exactf_negative_posix;
    dispatch[EXACTFU][NPOSIXU] = compare_exactf_negative_posix;
    dispatch[NOTHING][NPOSIXU] = compare_left_tail;
    dispatch[STAR][NPOSIXU] = compare_mismatch;
    dispatch[PLUS][NPOSIXU] = compare_left_plus;
    dispatch[CURLY][NPOSIXU] = compare_left_curly;
    dispatch[CURLYM][NPOSIXU] = compare_left_curly;
    dispatch[CURLYX][NPOSIXU] = compare_left_curly;
    dispatch[OPEN][NPOSIXU] = compare_left_open;
    dispatch[CLOSE][NPOSIXU] = compare_left_tail;
    dispatch[IFMATCH][NPOSIXU] = compare_after_assertion;
    dispatch[UNLESSM][NPOSIXU] = compare_after_assertion;
    dispatch[MINMOD][NPOSIXU] = compare_left_tail;
    dispatch[OPTIMIZED][NPOSIXU] = compare_left_tail;

    dispatch[SUCCEED][NPOSIXA] = compare_left_tail;
    dispatch[BOL][NPOSIXA] = compare_bol;
    dispatch[MBOL][NPOSIXA] = compare_bol;
    dispatch[SBOL][NPOSIXA] = compare_bol;
    dispatch[BOUND][NPOSIXA] = compare_mismatch;
    dispatch[NBOUND][NPOSIXA] = compare_mismatch;
    dispatch[REG_ANY][NPOSIXA] = compare_mismatch;
    dispatch[SANY][NPOSIXA] = compare_mismatch;
    dispatch[ANYOF][NPOSIXA] = compare_anyof_negative_posix;
    dispatch[POSIXD][NPOSIXA] = compare_posix_negative_posix;
    dispatch[POSIXU][NPOSIXA] = compare_posix_negative_posix;
    dispatch[POSIXA][NPOSIXA] = compare_posix_negative_posix;
    dispatch[NPOSIXD][NPOSIXA] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXU][NPOSIXA] = compare_negative_posix_negative_posix;
    dispatch[NPOSIXA][NPOSIXA] = compare_negative_posix_negative_posix;
    dispatch[BRANCH][NPOSIXA] = compare_left_branch;
    dispatch[EXACT][NPOSIXA] = compare_exact_negative_posix;
    dispatch[EXACTF][NPOSIXA] = compare_exactf_negative_posix;
    dispatch[EXACTFU][NPOSIXA] = compare_exactf_negative_posix;
    dispatch[NOTHING][NPOSIXA] = compare_left_tail;
    dispatch[STAR][NPOSIXA] = compare_mismatch;
    dispatch[PLUS][NPOSIXA] = compare_left_plus;
    dispatch[CURLY][NPOSIXA] = compare_left_curly;
    dispatch[CURLYM][NPOSIXA] = compare_left_curly;
    dispatch[CURLYX][NPOSIXA] = compare_left_curly;
    dispatch[OPEN][NPOSIXA] = compare_left_open;
    dispatch[CLOSE][NPOSIXA] = compare_left_tail;
    dispatch[IFMATCH][NPOSIXA] = compare_after_assertion;
    dispatch[UNLESSM][NPOSIXA] = compare_after_assertion;
    dispatch[MINMOD][NPOSIXA] = compare_left_tail;
    dispatch[OPTIMIZED][NPOSIXA] = compare_left_tail;
#endif

    for (i = 0; i < REGNODE_MAX; ++i)
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][EXACT] = compare_mismatch;
    dispatch[ALNUMA][EXACT] = compare_mismatch;
    dispatch[NALNUM][EXACT] = compare_mismatch;
    dispatch[NALNUMA][EXACT] = compare_mismatch;
    dispatch[SPACE][EXACT] = compare_mismatch;
    dispatch[SPACEA][EXACT] = compare_mismatch;
    dispatch[NSPACE][EXACT] = compare_mismatch;
    dispatch[NSPACEA][EXACT] = compare_mismatch;
    dispatch[DIGIT][EXACT] = compare_mismatch;
    dispatch[DIGITA][EXACT] = compare_mismatch;
    dispatch[NDIGIT][EXACT] = compare_mismatch;
    dispatch[NDIGITA][EXACT] = compare_mismatch;
#else
    dispatch[POSIXD][EXACT] = compare_mismatch;
    dispatch[POSIXU][EXACT] = compare_mismatch;
    dispatch[POSIXA][EXACT] = compare_mismatch;
    dispatch[NPOSIXD][EXACT] = compare_mismatch;
    dispatch[NPOSIXU][EXACT] = compare_mismatch;
    dispatch[NPOSIXA][EXACT] = compare_mismatch;
#endif
    dispatch[BRANCH][EXACT] = compare_left_branch;
    dispatch[EXACT][EXACT] = compare_exact_exact;
    dispatch[EXACTF][EXACT] = compare_exactf_exact;
    dispatch[EXACTFU][EXACT] = compare_exactf_exact;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][EXACT] = compare_mismatch;
    dispatch[NVERTWS][EXACT] = compare_mismatch;
    dispatch[HORIZWS][EXACT] = compare_mismatch;
    dispatch[NHORIZWS][EXACT] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][EXACTF] = compare_mismatch;
    dispatch[ALNUMA][EXACTF] = compare_mismatch;
    dispatch[NALNUM][EXACTF] = compare_mismatch;
    dispatch[NALNUMA][EXACTF] = compare_mismatch;
    dispatch[SPACE][EXACTF] = compare_mismatch;
    dispatch[SPACEA][EXACTF] = compare_mismatch;
    dispatch[NSPACE][EXACTF] = compare_mismatch;
    dispatch[NSPACEA][EXACTF] = compare_mismatch;
    dispatch[DIGIT][EXACTF] = compare_mismatch;
    dispatch[DIGITA][EXACTF] = compare_mismatch;
    dispatch[NDIGIT][EXACTF] = compare_mismatch;
    dispatch[NDIGITA][EXACTF] = compare_mismatch;
#else
    dispatch[POSIXD][EXACTF] = compare_mismatch;
    dispatch[POSIXU][EXACTF] = compare_mismatch;
    dispatch[POSIXA][EXACTF] = compare_mismatch;
    dispatch[NPOSIXD][EXACTF] = compare_mismatch;
    dispatch[NPOSIXU][EXACTF] = compare_mismatch;
    dispatch[NPOSIXA][EXACTF] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][EXACTF] = compare_mismatch;
    dispatch[NVERTWS][EXACTF] = compare_mismatch;
    dispatch[HORIZWS][EXACTF] = compare_mismatch;
    dispatch[NHORIZWS][EXACTF] = compare_mismatch;
#endif
    dispatch[OPTIMIZED][EXACTF] = compare_left_tail;

    dispatch[SUCCEED][EXACTFU] = compare_left_tail;
    dispatch[BOL][EXACTFU] = compare_bol;
    dispatch[MBOL][EXACTFU] = compare_bol;
    dispatch[SBOL][EXACTFU] = compare_bol;
    dispatch[BOUND][EXACTFU] = compare_mismatch;
    dispatch[NBOUND][EXACTFU] = compare_mismatch;
    dispatch[REG_ANY][EXACTFU] = compare_mismatch;
    dispatch[SANY][EXACTFU] = compare_mismatch;
    dispatch[ANYOF][EXACTFU] = compare_anyof_exactf;
#ifdef RC_POSIX_NODES
    dispatch[POSIXD][EXACTFU] = compare_mismatch;
    dispatch[POSIXU][EXACTFU] = compare_mismatch;
    dispatch[POSIXA][EXACTFU] = compare_mismatch;
    dispatch[NPOSIXD][EXACTFU] = compare_mismatch;
    dispatch[NPOSIXU][EXACTFU] = compare_mismatch;
    dispatch[NPOSIXA][EXACTFU] = compare_mismatch;
#endif
    dispatch[BRANCH][EXACTFU] = compare_left_branch;
    dispatch[EXACT][EXACTFU] = compare_exact_exactf;
    dispatch[EXACTFU][EXACTFU] = compare_exactf_exactf;
    dispatch[NOTHING][EXACTFU] = compare_left_tail;
    dispatch[STAR][EXACTFU] = compare_mismatch;
    dispatch[PLUS][EXACTFU] = compare_left_plus;
    dispatch[CURLY][EXACTFU] = compare_left_curly;
    dispatch[CURLYM][EXACTFU] = compare_left_curly;
    dispatch[CURLYX][EXACTFU] = compare_left_curly;
    dispatch[OPEN][EXACTFU] = compare_left_open;
    dispatch[CLOSE][EXACTFU] = compare_left_tail;
    dispatch[IFMATCH][EXACTFU] = compare_after_assertion;
    dispatch[UNLESSM][EXACTFU] = compare_after_assertion;
    dispatch[MINMOD][EXACTFU] = compare_left_tail;
    dispatch[OPTIMIZED][EXACTFU] = compare_left_tail;

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
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

    for (i = 0; i < REGNODE_MAX; ++i)
    {
	dispatch[i][OPEN] = compare_right_open;
    }

    dispatch[OPEN][OPEN] = compare_open_open;

    for (i = 0; i < REGNODE_MAX; ++i)
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][IFMATCH] = compare_mismatch;
    dispatch[ALNUMA][IFMATCH] = compare_mismatch;
    dispatch[NALNUM][IFMATCH] = compare_mismatch;
    dispatch[NALNUMA][IFMATCH] = compare_mismatch;
    dispatch[SPACE][IFMATCH] = compare_mismatch;
    dispatch[SPACEA][IFMATCH] = compare_mismatch;
    dispatch[NSPACE][IFMATCH] = compare_mismatch;
    dispatch[NSPACEA][IFMATCH] = compare_mismatch;
    dispatch[DIGIT][IFMATCH] = compare_mismatch;
    dispatch[DIGITA][IFMATCH] = compare_mismatch;
    dispatch[NDIGIT][IFMATCH] = compare_mismatch;
    dispatch[NDIGITA][IFMATCH] = compare_mismatch;
#else
    dispatch[POSIXD][IFMATCH] = compare_mismatch;
    dispatch[POSIXU][IFMATCH] = compare_mismatch;
    dispatch[POSIXA][IFMATCH] = compare_mismatch;
    dispatch[NPOSIXD][IFMATCH] = compare_mismatch;
    dispatch[NPOSIXU][IFMATCH] = compare_mismatch;
    dispatch[NPOSIXA][IFMATCH] = compare_mismatch;
#endif
    dispatch[BRANCH][IFMATCH] = compare_mismatch;
    dispatch[EXACT][IFMATCH] = compare_mismatch;
    dispatch[EXACTF][IFMATCH] = compare_mismatch;
    dispatch[EXACTFU][IFMATCH] = compare_mismatch;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][IFMATCH] = compare_mismatch;
    dispatch[NVERTWS][IFMATCH] = compare_mismatch;
    dispatch[HORIZWS][IFMATCH] = compare_mismatch;
    dispatch[NHORIZWS][IFMATCH] = compare_mismatch;
#endif
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
#ifndef RC_POSIX_NODES
    dispatch[ALNUM][UNLESSM] = compare_mismatch;
    dispatch[ALNUMA][UNLESSM] = compare_mismatch;
    dispatch[NALNUM][UNLESSM] = compare_mismatch;
    dispatch[NALNUMA][UNLESSM] = compare_mismatch;
    dispatch[SPACE][UNLESSM] = compare_mismatch;
    dispatch[SPACEA][UNLESSM] = compare_mismatch;
    dispatch[NSPACE][UNLESSM] = compare_mismatch;
    dispatch[NSPACEA][UNLESSM] = compare_mismatch;
    dispatch[DIGIT][UNLESSM] = compare_mismatch;
    dispatch[DIGITA][UNLESSM] = compare_mismatch;
    dispatch[NDIGIT][UNLESSM] = compare_mismatch;
    dispatch[NDIGITA][UNLESSM] = compare_mismatch;
#else
    dispatch[POSIXD][UNLESSM] = compare_mismatch;
    dispatch[POSIXU][UNLESSM] = compare_mismatch;
    dispatch[POSIXA][UNLESSM] = compare_mismatch;
    dispatch[NPOSIXD][UNLESSM] = compare_mismatch;
    dispatch[NPOSIXU][UNLESSM] = compare_mismatch;
    dispatch[NPOSIXA][UNLESSM] = compare_mismatch;
#endif
    dispatch[BRANCH][UNLESSM] = compare_mismatch;
    dispatch[EXACT][UNLESSM] = compare_mismatch;
    dispatch[EXACTF][UNLESSM] = compare_mismatch;
    dispatch[EXACTFU][UNLESSM] = compare_mismatch;
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
#ifndef RC_POSIX_NODES
    dispatch[VERTWS][UNLESSM] = compare_mismatch;
    dispatch[NVERTWS][UNLESSM] = compare_mismatch;
    dispatch[HORIZWS][UNLESSM] = compare_mismatch;
    dispatch[NHORIZWS][UNLESSM] = compare_mismatch;
#endif
    dispatch[OPTIMIZED][UNLESSM] = compare_left_tail;

    for (i = 0; i < REGNODE_MAX; ++i)
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

#ifndef RC_POSIX_NODES
    dispatch[SUCCEED][VERTWS] = compare_left_tail;
    dispatch[BOL][VERTWS] = compare_bol;
    dispatch[MBOL][VERTWS] = compare_bol;
    dispatch[SBOL][VERTWS] = compare_bol;
    dispatch[BOUND][VERTWS] = compare_mismatch;
    dispatch[NBOUND][VERTWS] = compare_mismatch;
    dispatch[REG_ANY][VERTWS] = compare_mismatch;
    dispatch[SANY][VERTWS] = compare_mismatch;
    dispatch[ANYOF][VERTWS] = compare_anyof_vertical_space;
    dispatch[ALNUM][VERTWS] = compare_mismatch;
    dispatch[ALNUMA][VERTWS] = compare_mismatch;
    dispatch[NALNUM][VERTWS] = compare_mismatch;
    dispatch[NALNUMA][VERTWS] = compare_mismatch;
    dispatch[SPACE][VERTWS] = compare_mismatch;
    dispatch[SPACEA][VERTWS] = compare_mismatch;
    dispatch[NSPACE][VERTWS] = compare_mismatch;
    dispatch[NSPACEA][VERTWS] = compare_mismatch;
    dispatch[DIGIT][VERTWS] = compare_mismatch;
    dispatch[DIGITA][VERTWS] = compare_mismatch;
    dispatch[NDIGIT][VERTWS] = compare_mismatch;
    dispatch[NDIGITA][VERTWS] = compare_mismatch;
    dispatch[BRANCH][VERTWS] = compare_left_branch;
    dispatch[EXACT][VERTWS] = compare_exact_vertical_space;
    dispatch[EXACTF][VERTWS] = compare_exact_vertical_space;
    dispatch[NOTHING][VERTWS] = compare_left_tail;
    dispatch[TAIL][VERTWS] = compare_left_tail;
    dispatch[STAR][VERTWS] = compare_mismatch;
    dispatch[PLUS][VERTWS] = compare_left_plus;
    dispatch[CURLY][VERTWS] = compare_left_curly;
    dispatch[CURLYM][VERTWS] = compare_left_curly;
    dispatch[CURLYX][VERTWS] = compare_left_curly;
    dispatch[WHILEM][VERTWS] = compare_left_tail;
    dispatch[OPEN][VERTWS] = compare_left_open;
    dispatch[CLOSE][VERTWS] = compare_left_tail;
    dispatch[IFMATCH][VERTWS] = compare_after_assertion;
    dispatch[UNLESSM][VERTWS] = compare_after_assertion;
    dispatch[MINMOD][VERTWS] = compare_left_tail;
    dispatch[VERTWS][VERTWS] = compare_tails;
    dispatch[NVERTWS][VERTWS] = compare_mismatch;
    dispatch[HORIZWS][VERTWS] = compare_mismatch;
    dispatch[NHORIZWS][VERTWS] = compare_mismatch;
    dispatch[OPTIMIZED][VERTWS] = compare_left_tail;

    dispatch[SUCCEED][NVERTWS] = compare_left_tail;
    dispatch[BOL][NVERTWS] = compare_bol;
    dispatch[MBOL][NVERTWS] = compare_bol;
    dispatch[SBOL][NVERTWS] = compare_bol;
    dispatch[BOUND][NVERTWS] = compare_mismatch;
    dispatch[NBOUND][NVERTWS] = compare_mismatch;
    dispatch[REG_ANY][NVERTWS] = compare_mismatch;
    dispatch[SANY][NVERTWS] = compare_mismatch;
    dispatch[ANYOF][NVERTWS] = compare_anyof_negative_vertical_space;
    dispatch[ALNUM][NVERTWS] = compare_tails;
    dispatch[ALNUMA][NVERTWS] = compare_tails;
    dispatch[NALNUM][NVERTWS] = compare_mismatch;
    dispatch[NALNUMA][NVERTWS] = compare_mismatch;
    dispatch[SPACE][NVERTWS] = compare_mismatch;
    dispatch[SPACEA][NVERTWS] = compare_mismatch;
    dispatch[NSPACE][NVERTWS] = compare_mismatch;
    dispatch[NSPACEA][NVERTWS] = compare_mismatch;
    dispatch[DIGIT][NVERTWS] = compare_tails;
    dispatch[DIGITA][NVERTWS] = compare_tails;
    dispatch[NDIGIT][NVERTWS] = compare_mismatch;
    dispatch[NDIGITA][NVERTWS] = compare_mismatch;
    dispatch[BRANCH][NVERTWS] = compare_left_branch;
    dispatch[EXACT][NVERTWS] = compare_exact_negative_vertical_space;
    dispatch[EXACTF][NVERTWS] = compare_exact_negative_vertical_space;
    dispatch[NOTHING][NVERTWS] = compare_left_tail;
    dispatch[TAIL][NVERTWS] = compare_left_tail;
    dispatch[STAR][NVERTWS] = compare_mismatch;
    dispatch[PLUS][NVERTWS] = compare_left_plus;
    dispatch[CURLY][NVERTWS] = compare_left_curly;
    dispatch[CURLYM][NVERTWS] = compare_left_curly;
    dispatch[CURLYX][NVERTWS] = compare_left_curly;
    dispatch[WHILEM][NVERTWS] = compare_left_tail;
    dispatch[OPEN][NVERTWS] = compare_left_open;
    dispatch[CLOSE][NVERTWS] = compare_left_tail;
    dispatch[IFMATCH][NVERTWS] = compare_after_assertion;
    dispatch[UNLESSM][NVERTWS] = compare_after_assertion;
    dispatch[MINMOD][NVERTWS] = compare_left_tail;
    dispatch[VERTWS][NVERTWS] = compare_mismatch;
    dispatch[NVERTWS][NVERTWS] = compare_tails;
    dispatch[HORIZWS][NVERTWS] = compare_mismatch;
    dispatch[NHORIZWS][NVERTWS] = compare_mismatch;
    dispatch[OPTIMIZED][NVERTWS] = compare_left_tail;

    dispatch[SUCCEED][HORIZWS] = compare_left_tail;
    dispatch[BOL][HORIZWS] = compare_bol;
    dispatch[MBOL][HORIZWS] = compare_bol;
    dispatch[SBOL][HORIZWS] = compare_bol;
    dispatch[BOUND][HORIZWS] = compare_mismatch;
    dispatch[NBOUND][HORIZWS] = compare_mismatch;
    dispatch[REG_ANY][HORIZWS] = compare_mismatch;
    dispatch[SANY][HORIZWS] = compare_mismatch;
    dispatch[ANYOF][HORIZWS] = compare_anyof_horizontal_space;
    dispatch[ALNUM][HORIZWS] = compare_mismatch;
    dispatch[ALNUMA][HORIZWS] = compare_mismatch;
    dispatch[NALNUM][HORIZWS] = compare_mismatch;
    dispatch[NALNUMA][HORIZWS] = compare_mismatch;
    dispatch[SPACE][HORIZWS] = compare_mismatch;
    dispatch[SPACEA][HORIZWS] = compare_mismatch;
    dispatch[NSPACE][HORIZWS] = compare_mismatch;
    dispatch[NSPACEA][HORIZWS] = compare_mismatch;
    dispatch[DIGIT][HORIZWS] = compare_mismatch;
    dispatch[DIGITA][HORIZWS] = compare_mismatch;
    dispatch[NDIGIT][HORIZWS] = compare_mismatch;
    dispatch[NDIGITA][HORIZWS] = compare_mismatch;
    dispatch[BRANCH][HORIZWS] = compare_left_branch;
    dispatch[EXACT][HORIZWS] = compare_exact_horizontal_space;
    dispatch[EXACTF][HORIZWS] = compare_exact_horizontal_space;
    dispatch[NOTHING][HORIZWS] = compare_left_tail;
    dispatch[TAIL][HORIZWS] = compare_left_tail;
    dispatch[STAR][HORIZWS] = compare_mismatch;
    dispatch[PLUS][HORIZWS] = compare_left_plus;
    dispatch[CURLY][HORIZWS] = compare_left_curly;
    dispatch[CURLYM][HORIZWS] = compare_left_curly;
    dispatch[CURLYX][HORIZWS] = compare_left_curly;
    dispatch[WHILEM][HORIZWS] = compare_left_tail;
    dispatch[OPEN][HORIZWS] = compare_left_open;
    dispatch[CLOSE][HORIZWS] = compare_left_tail;
    dispatch[IFMATCH][HORIZWS] = compare_after_assertion;
    dispatch[UNLESSM][HORIZWS] = compare_after_assertion;
    dispatch[MINMOD][HORIZWS] = compare_left_tail;
    dispatch[VERTWS][HORIZWS] = compare_mismatch;
    dispatch[NVERTWS][HORIZWS] = compare_mismatch;
    dispatch[HORIZWS][HORIZWS] = compare_tails;
    dispatch[NHORIZWS][HORIZWS] = compare_mismatch;
    dispatch[OPTIMIZED][HORIZWS] = compare_left_tail;

    dispatch[SUCCEED][NHORIZWS] = compare_left_tail;
    dispatch[BOL][NHORIZWS] = compare_bol;
    dispatch[MBOL][NHORIZWS] = compare_bol;
    dispatch[SBOL][NHORIZWS] = compare_bol;
    dispatch[BOUND][NHORIZWS] = compare_mismatch;
    dispatch[NBOUND][NHORIZWS] = compare_mismatch;
    dispatch[REG_ANY][NHORIZWS] = compare_mismatch;
    dispatch[SANY][NHORIZWS] = compare_mismatch;
    dispatch[ANYOF][NHORIZWS] = compare_anyof_negative_horizontal_space;
    dispatch[ALNUM][NHORIZWS] = compare_tails;
    dispatch[ALNUMA][NHORIZWS] = compare_tails;
    dispatch[NALNUM][NHORIZWS] = compare_mismatch;
    dispatch[NALNUMA][NHORIZWS] = compare_mismatch;
    dispatch[SPACE][NHORIZWS] = compare_mismatch;
    dispatch[SPACEA][NHORIZWS] = compare_mismatch;
    dispatch[NSPACE][NHORIZWS] = compare_tails;
    dispatch[NSPACEA][NHORIZWS] = compare_mismatch;
    dispatch[DIGIT][NHORIZWS] = compare_tails;
    dispatch[DIGITA][NHORIZWS] = compare_tails;
    dispatch[NDIGIT][NHORIZWS] = compare_mismatch;
    dispatch[NDIGITA][NHORIZWS] = compare_mismatch;
    dispatch[BRANCH][NHORIZWS] = compare_left_branch;
    dispatch[EXACT][NHORIZWS] = compare_exact_negative_horizontal_space;
    dispatch[EXACTF][NHORIZWS] = compare_exact_negative_horizontal_space;
    dispatch[NOTHING][NHORIZWS] = compare_left_tail;
    dispatch[TAIL][NHORIZWS] = compare_left_tail;
    dispatch[STAR][NHORIZWS] = compare_mismatch;
    dispatch[PLUS][NHORIZWS] = compare_left_plus;
    dispatch[CURLY][NHORIZWS] = compare_left_curly;
    dispatch[CURLYM][NHORIZWS] = compare_left_curly;
    dispatch[CURLYX][NHORIZWS] = compare_left_curly;
    dispatch[WHILEM][NHORIZWS] = compare_left_tail;
    dispatch[OPEN][NHORIZWS] = compare_left_open;
    dispatch[CLOSE][NHORIZWS] = compare_left_tail;
    dispatch[IFMATCH][NHORIZWS] = compare_after_assertion;
    dispatch[UNLESSM][NHORIZWS] = compare_after_assertion;
    dispatch[MINMOD][NHORIZWS] = compare_left_tail;
    dispatch[VERTWS][NHORIZWS] = compare_mismatch;
    dispatch[NVERTWS][NHORIZWS] = compare_mismatch;
    dispatch[HORIZWS][NHORIZWS] = compare_mismatch;
    dispatch[NHORIZWS][NHORIZWS] = compare_tails;
    dispatch[OPTIMIZED][NHORIZWS] = compare_left_tail;
#endif

    for (i = 0; i < REGNODE_MAX; ++i)
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
