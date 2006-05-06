# Before `make install' is performed this script should be runnable with
# `make test'. After `make install' it should work as `perl Regexp-Compare.t'

use strict;

use Regexp::Compare qw(is_less_or_equal);

our @leq;
our @nc;
our @invalid;
our $i;

BEGIN {
    @leq = (
	    '' => '', 'a' => '', 'a' => 'a', 'a' => '(?:b|)a',
 	    'aa' => 'a', 'abc' => 'bc', 'abc' => 'ab', '[a]' => 'a',
 	    'a' => '[a]', 'ab' => '[ab]', '[a]' => '[a]', '[a]' => '[ab]', 
 	    'a' => '[^b]', 'a' => '.', '[a]' => '.', '[a][b]' => 'ab',
	    'ab' => '[a][b]', 'a|b' => '[ab]', 'a' => 'a|b',
	    'ab[c]' => 'abc', '.' => '[^\\n]', '[^\\n]' => '.',
	    '[ab]' => 'a|b', 'a|b' => 'a|b', 'a' => 'a?', 'aa' => 'a?',
	    'a' => 'a{1,2}', 'a' => 'a*', 'aa' => 'a*', 'aaa' => 'a*',
	    'a*' => 'a*', 'a*b' => 'a*b', 'ab*c' => 'ab*c', 'a{1,2}' => 'a*',
	    'a*' => 'a*', 'a' => 'a+', 'aa' => 'a+', 'a?' => 'a{0,1}',
	    'a{0,1}' => 'a?', 'a{1,}' => 'a', 'a{2,}' => '(?i:a)',
	    'a{1,}' => 'a+', 'a{2,3}' => 'a+', 'ab+c' => 'ab+c',
	    'a' => 'a{1,}', 'a{1,}' => '\\w', '(?:^a){1,}' => '^a',
	    'a+' => 'a{1,}', 'a*' => 'a{0,}', 'a{0,}' => 'a*', 'a+b' => 'ab',
	    'ab+' => 'ab{0,}', 'ab+c' => 'ab{1,}c', 'ab{1}c' => 'abc',
	    'ab{1}c' => 'ad*bc', 'abc' => '(?:abc){1,2}',
	    'a[b]c' => '(?i:abc){2}', 'ab+c' => 'ab*c',
	    'aaa' => 'a+', '^a+a' => '^aa', 'ab' => '(?:ab)*',
	    'a*' => 'a*|b*', 'a*b' => '.', 'a*-' => '\\W',
	    '.+' => '.', '\\d+' => '\\d', '\\d' => '[0-9]',
	    '[0-9]' => '\\d', '[23]' => '\\d', '4' => '\\d',
	    '\\d' => '.', '[ \\t]' => '\\s', ' ' => '\\s',
	    'a' => '\\S', '[a]' => '\\S', '\\S' => '.', '\\S\\S' => '\\S',
	    '(?i:a)' => '[aA]', '[aA]' => '(?i:a)', '(?i: )' => '(?i: )',
	    '(?i:a)' => '(?i:a)', '(?i:a)' => '(?i:A)', '(?i:A)' => '(?i:a)',
	    '(?i:a)' => '\\w', '(?i:0)' => '\\d',
	    'c\\d' => '\\d', 'a[bc]d' => '[bc]', '\\s.' => '.',
	    '.\\s' => '.', '.\\s' => '\\s', '\\s ' => ' ', 'a' => '[\\S]',
	    '\\d' => '\\w', '(?i:a)' => '\\w', '\\d' => '\\w',
	    '\\D' => '[^0-9]', '[^0-9]' => '\\D', '\\W' => '\\D',
	    '\\d' => '[0-9]', '[0-9]' => '\\d', '[0-9a-zA-Z_]' => '\\w',
	    '\\w' => '[0-9a-zA-Z_]',
	    '\\W+' => '\\D', '^\\w+a' => '^\\w\\w', 'abc' => '\\w+',
	    '(?i:abc)' => '\\w+', '(?:0+|1)' => '\\d+',
	    '.' => '(?s:.)', '^a' => 'a', '^.a' => 'a', '(?s:^a)' => '^a',
	    '^a' => '(?s:^a)', '^a' => '(?m:^a)', '(?m:^a)' => '(?m:^a)',
	    '\\na' => '(?m:^a)', '(?m:[\\n]a)' => '(?m:^a)',
	    '(?m:\\n[a])' => '(?m:^a)', '(?m:\\n\\n[a])' => '(?m:^a)',
	    'a\\nb' => '(?m:^b)',
	    '.\\nb' => '(?m:^b)', '[a-z]\\nb' => '(?m:^b)', 'a$' => 'a',
	    'a$' => 'a$', 'aa$' => 'a$', 'a$' => 'a(?:b|)',
	    'a$' => 'a(?:b|)$', 'a[\\n]' => '(?m:a$)', '^$' => '^$',
	    '^a' => '\\b',
	    '^[a-c]' => '\\b\\w', '[a-z]-' => '\\b-', '[+-]\\d' => '\\b',
	    '-$' => '\\B', '\\B' => '\\B', 'a\\d' => '\\B', '\\da' => '\\B',
	    '(?:(?:a|b)|(?:c|d))' => '[a-d]',
	    '[a-d]' => '(?:(?:a|b)|(?:c|d))', '(?:a[b])+' => '\\w*',
	    '(?:a|b)(?:c|d)' => '[ab][cd]', '(?:b|)' => '(?:b|)',
	   );
# thinks that should match but it isn't clear how to make them:
# 'aa*b' => 'ab', 'aa*' => 'a+', '(?:(?:abc){1,2})+' => '\\w+',
# '(?:aa)+' => 'a{2,}', 'a+a+' => 'a{2,}'
# 23Apr2006: ('a', '[^\\s]') doesn't match - shouldn't it?

    my %known;
    $i = 0;
    while ($i < scalar(@leq)) {
	$known{$leq[$i]}->{$leq[$i + 1]} = 1;
	$i += 2;
    }

    # test reflexivity

    my $cnt = scalar(@leq);
    $i = 0;
    while ($i < $cnt) {
	my $rx = $leq[$i];
	if (!exists($known{$rx}) ||
	    !exists($known{$rx}->{$rx})) {
	    $known{$rx}->{$rx} = 1;
	    push @leq, ($rx, $rx);
	}

	++$i;
    }

    # test transitivity

    my $double = 0;
    my %chain;
    while ($double < scalar(@leq)) {
	$double = scalar(@leq);

	%chain = ();
	$i = 0;
	while ($i < $double) {
	    $chain{$leq[$i + 1]} = {
				    left => $leq[$i],
				    right => { }
				   };
	    $i += 2;
	}

	$i = 0;
	while ($i < $double) {
	    if (exists($chain{$leq[$i]})) {
		$chain{$leq[$i]}->{right}->{$leq[$i + 1]} = 1;
	    }

	    $i += 2;
	}

	$i = 0;
	while ($i < $double) {
	    delete $chain{$leq[$i + 1]}->{right}->{$leq[$i + 1]};
	    if (!scalar(keys %{$chain{$leq[$i + 1]}->{right}})) {
		delete $chain{$leq[$i + 1]};
	    }

	    $i += 2;
	}

	foreach my $t (sort keys %chain) {
	    my $l = $chain{$t}->{left};
	    foreach my $r (sort keys %{$chain{$t}->{right}}) {
		if (!exists($known{$l}) ||
		    !exists($known{$l}->{$r})) {
		    $known{$l}->{$r} = 1;
		    push @leq, ($l, $r);
		}
	    }
	}
    }

    @nc = (
	   '' => 'a', 'a' => 'b', 'abc' => 'ac',
	   '[ab]' => 'ab', '.' => 'a',	'.' => '[a]', '\\d' => '[a]',
	   'a' => '\\d',
	   '\\d' => '[23]', '\\d' => '4', '.' => '\\d', '\\s' => 'a',
	   '\\s' => '[ \\t]', '\\s' => ' ', '.' => '\\s', '\\s' => '.',
	   '\\S' => 'a', '.' => '\\S', '\\S' => '\\S\\S', '\\n' => '.',
	   '[\\n]' => '.', '.' => '\\s', '\\D' => '\\W', '(?s:.)' => '.',
	   '(?m:^a)' => '^a', '(?i:a)' => '\\W', '(?i:0)' => '\\D',
	   'a[bc]de' => '[bc]e', 'a' => '^a', '[a-z]' => '^a',
	   'a+' => 'a{2,}', 'ab+c' => 'abc', 'a+' => 'aaa', 
	   '(?:^a)*' => '^a', 'ab+c' => 'ab{2,}c', '[a ]' => '\\b',
	   '\\B' => '\\b', '\\w+' => 'abc', '\\w{3,}' => 'abc',
	   '\\d{1,}' => '0+', 'a+' => '\\d+', 'a+' => 'b{1,}',
	  );

    @invalid = ( 'a' => '[a', 'a{2,1}' => 'a' );
}

use Test::More tests => (scalar(@leq) / 2) + (scalar(@nc) / 2) + (scalar(@invalid) / 2);

$i = 0;
while ($i < scalar(@leq)) {
#   warn 'testing ' . $leq[$i] . ' <= ' . $leq[$i + 1] . "\n";
    ok(is_less_or_equal($leq[$i], $leq[$i + 1]),
       '/' . $leq[$i] . '/ <= /' . $leq[$i + 1] . '/');
    $i += 2;
}

$i = 0;
while ($i < scalar(@nc)) {
    ok(!is_less_or_equal($nc[$i], $nc[$i + 1]),
       '/' . $nc[$i] . '/ ? /' . $nc[$i + 1] . '/');
    $i += 2;
}

$i = 0;
while ($i < scalar(@invalid)) {
    eval { 
	is_less_or_equal($invalid[$i], $invalid[$i + 1]);
    };
    ok($@);
    $i += 2;
}
