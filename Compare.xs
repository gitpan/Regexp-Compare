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
	regexp *r1 = 0, *r2 = 0;
	int rv;

	ENTER;
	SAVEDESTRUCTOR(rc_regfree, r1);
	SAVEDESTRUCTOR(rc_regfree, r2);

	r1 = rc_regcomp(rs1);
	r2 = rc_regcomp(rs2);
	rv = rc_compare(r1->program, r2->program);

	LEAVE;

	if (rv < 0)
	{
		croak(rc_error ? rc_error : "Regexp comparison failed");
	}

        RETVAL = newSViv(rv);
        }
        OUTPUT:
        RETVAL
