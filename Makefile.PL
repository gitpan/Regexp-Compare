require 5.014_000;

use ExtUtils::MakeMaker;
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.

WriteMakefile(
    NAME              => 'Regexp::Compare',
    VERSION_FROM      => 'lib/Regexp/Compare.pm', # finds $VERSION
    PREREQ_PM         => {}, # e.g., Module::Name => 1.1
    ABSTRACT_FROM     => 'lib/Regexp/Compare.pm', # retrieve abstract from module
    AUTHOR            => 'Vaclav Barta <vbar@comp.cz>',
    LIBS              => [''], # e.g., '-lm'
    DEFINE            => '', # e.g., '-DHAVE_SOMETHING'
    INC               => '-I.', # e.g., '-I. -I/usr/include/other'
    OBJECT            => 'Compare.o engine.o',
    'depend'	      => {
			  'engine.o' => 'engine.c engine.h',
			 },
);
