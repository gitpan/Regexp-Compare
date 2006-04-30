#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"
#include "engine.h"


MODULE = Regexp::Compare		PACKAGE = Regexp::Compare

PROTOTYPES: ENABLE

BOOT:
rc_init();

SV *
_is_less_or_equal(rs1, rs2)
        char *rs1;
        char *rs2;
        CODE:
        {
	regexp *r1, *r2;
	int rv;

	if (!rs1 || !rs2)
	{
		croak("No regexp to compare");
	}

	r1 = rc_regcomp(rs1);
	if (!r1)
	{
		croak("Cannot compile regexp");
	}

	r2 = rc_regcomp(rs2);
	if (!r2)
	{
		pregfree(r1);
		croak("Can't compile regexp");
	}

	rv = rc_compare(r1->program, r2->program);

	pregfree(r1);
	pregfree(r2);

	if (rv < 0)
	{
		croak(rc_error ? rc_error : "Regexp comparison failed");
	}

        RETVAL = newSViv(rv);
        }
        OUTPUT:
        RETVAL
