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
	    '' => '', '|||' => '', '' => '|||', 'a' => '', 'a' => '(?:b|)a',
 	    'aa' => 'a', 'abc' => 'bc', 'abc' => 'ab', 'abcd' => 'bc',
	    '[a]' => 'a', 'a' => '[a]', 'ab' => '[ab]', '[a]' => '[ab]',
 	    'a' => '[^b]', 'a' => '.', '[a]' => '.', '[a][b]' => 'ab',
	    'ab' => '[a][b]', 'a|b' => '[ab]', 'a' => 'a|b',
	    'ab[c]' => 'abc', '.' => '[^\\n]', '[^\\n]' => '.',
	    'a' => '[^\\s]', '[^\\s]' => '(?s:.)', '[^\\S]' => '(?s:.)',
	    'a[^\\n]' => 'a(?s:.)', 'ac' => 'a(?:b|)c',
	    '[ab]' => 'a|b', '[a-c]' => 'a|b|c', 'a|b' => 'b|a',
	    'a' => 'a?', 'aa' => 'a?', '\\\\\\\\' => '\\\\',
	    '\\\\' => '\\W',
	    'a' => 'a{1,2}', 'a' => 'a*', 'aa' => 'a*', 'aaa' => 'a*',
	    'b\\d' => 'a*b\\d', 'ac' => 'ab*c', 'a{1,2}' => 'a*',
	    'a' => 'a+', 'aa' => 'a+', 'a?' => 'a{0,1}',
	    'a{0,1}' => 'a?', 'aa' => 'a{2}', 'a{2}' => 'aa',
	    'ab{2}c' => 'abbc', 'abbc' => 'ab{2}c',
	    'a{1,}' => 'a', 'a' => 'a{1,}', 'xay' => 'xa{1,}y',
	    'a{2,}' => '(?i:a)',
	    'a{1,}' => 'a+', 'a+' => 'a{1,}', 'a{2,3}' => 'a+', 'ab+' => 'a.',
	    'aa{0,}' => 'a{1,}', 'a{1,}' => 'aa{0,}', 'aa{0,}' => 'a+',
	    'a+' => 'aa{0,}', 'aa*' => 'a{1,}', 'a{1,}' => 'aa*',
	    'a{3,}' => 'a{2,}', '(?:abc){3,}' => '(?:abc){2,}',
	    'aa' => '(?s:.){2}', '(?i:aa)' => '(?s:.){2}',
	    'a(?i:a)' => '(?s:.){2}', 'a{,1}' => 'a\\W{2}\\d\\W',
	    'a+' => 'aa*', 'aa*' => 'a+', '[aA]' => '(?i:a)',
	    '(?i:a)' => '[aA]', '(?i:a)' => '[\\w]',
	    'a(?:bcd)+' => 'a(?i:bcd)', 'ab+c' => 'ab+.',
	    'ab(?:cd)+' => '(?:ab)+cd', '(?:ab)+cd' => 'ab(?:cd)+',
	    'a' => 'a{1,}', 'a{1,}' => '\\w', '(?:^a){1,}' => '^a',
	    'a+' => 'a{1,}', 'a*' => 'a{0,}', 'a{0,}' => 'a*', 'a+b' => 'ab',
	    'ab+' => 'ab{0,}', 'ab+' => 'a+b',
	    'ab+c' => 'ab{1,}c', 'ab{1}c' => 'abc',
	    'ab{1}c' => 'ad*bc', 'abc' => '(?:abc){1,2}', 'abc' => 'ab+c',
	    '(?i:abcd)' => '(?i:bc)',
	    'b{2,3}' => 'bb', 'b{3,3}' => 'bbb', 'a{1,}b' => 'ab',
	    'ab+c' => 'ab*c', 'aaa' => 'a+', 'ab' => 'a+b', 'aaab' => 'a+b',
	    '^a+a' => '^aa', 'ab' => '(?:ab)*', 'ab' => 'a*b',
	    'a*' => 'a*|b*', 'a*b' => '.', 'a*-' => '\\W', '1233*' => '123*',
	    '.+' => '.', '\\d+' => '\\d',
	    '[0-9]' => '\\d', '[23]' => '\\d', '4' => '\\d',
	    '0' => '\\w', '\\d' => '\\w',
	    '\\d' => '.', '[ \\t]' => '\\s', '[\\t ]' => '[^\\S]',
	    ' ' => '\\s', '\\w' => '[^\\s]', '\\W' => '[^a]',
	    'a' => '\\S', '[a]' => '\\S', '\\S' => '.', '\\S\\S' => '\\S',
	    '\\S' => '[^\\s]', '[^\\s]' => '\\S',
	    '(?i:a)' => '[aA]', '[aA]' => '(?i:a)', '(?i: )' => '(?i: )',
	    '(?i:a)' => '(?i:a)', '(?i:a)' => '(?i:A)', '(?i:A)' => '(?i:a)',
	    '(?i:a)' => '\\w', '(?i:0)' => '\\d',
	    'c\\d' => '\\d', 'a[bc]d' => '[bc]', '\\s.' => '.',
	    '.\\s' => '.', '.\\s' => '\\s', '\\s ' => ' ', 'a' => '[\\S]',
	    '\\s' => '[\\s]', '[\\s]' => '\\s', '\\S' => '[\\S]',
	    '[\\S]' => '\\S', '[^\\S]' => '\\s', '\\s' => '[^\\S]',
	    '\\w' => '[\\w]', '[\\w]' => '\\w',
	    '[^\\W]' => '\\w', '[^\\W]' => '\\w', '[^\\w]' => '\\W',
	    '\\W' => '[^\\w]', '[^\\d]' => '\\D', '\\D' => '[^\\d]',
	    '\\W' => '[\\W]', '[\\W]' => '\\W', '\\d' => '[\\d]',
	    '[\\d]' => '\\d', '(?i:-)' => '-',
	    '\\d' => '\\w', '(?i:a)' => '\\w', '\\d' => '\\w',
	    '\\D' => '[^0-9]', '\\D' => '[^0]',
	    '\\W' => '\\D', '\\d' => '[^\\D]', '[^\\D]' => '\\d',
	    '[0-9]' => '\\d', '[0-9a-zA-Z_]' => '\\w',
	    '(?i:ab)' => '..', '\\w\\d-' => '\\w-',
	    '\\W+' => '\\D', '^\\w+a' => '^\\w\\w', 'abc' => '\\w+',
	    '\\Aa' => '^a', '\\Aa' => '^a', '(?m:\\Aa)' => '^a',
	    '(?m:\\Aa)' => '^a', 'a\\Z' => 'a$', 'a$' => 'a\\Z',
	    '(?m:a\\Z)' => 'a$', 'a$' => '(?m:a\\Z)',	    
	    '(?i:abc)' => '\\w+', '(?i:abc)' => '[aA][bB][cC]',
	    '(?:0+|1)' => '\\d+',
	    '.' => '(?s:.)', '^a' => 'a', '^.a' => 'a', '(?s:^a)' => '^a',
	    '^a' => '(?s:^a)', '^a' => '(?m:^a)', '(?m:^a)' => '(?m:^a)',
	    '\\na' => '(?m:^a)', '(?m:[\\n]a)' => '(?m:^a)',
	    '(?m:\\n[a])' => '(?m:^a)', '(?m:\\n\\n[a])' => '(?m:^a)',
	    'a\\nb' => '(?m:^b)', '.\\nb' => '(?m:^b)',
	    '[a-z]\\nb' => '(?m:^b)', 'a$' => 'a', 'a$' => 'a$',
	    'aa$' => 'a$', '(?:abc)+$' => 'abc$', 'a$' => 'a(?:b|)',
	    'a$' => 'a(?:b|)$', 'a[\\n]' => '(?m:a$)', 'a$' => 'a*',
	    '^$' => '^$',
	    '^a' => '\\b', '\\ba' => 'a', 'a\\b' => 'a',
	    '^[a-c]' => '\\b\\w', '[a-z]-' => '\\b-', '[+-]\\d' => '\\b',
	    '-$' => '\\B', '^-' => '\\B', '^-$' => '\\B', 'a\\d' => '\\B',
	    '(?:a\\d){2}' => '\\B', '\\Ba' => 'a', '\\Baa' => 'a{1,2}',
	    '\\Baaaa' => '(?:aa){2}', '1(?:aa){2}' => '\\Baaaa',
	    '(?:aa){2}-' => 'aaaa',
	    '\\da' => '\\B', '(?:(?:a|b)|(?:c|d))' => '[a-d]',
	    '[a-d]' => '(?:(?:a|b)|(?:c|d))', '(?:a[b])+' => '\\w*',
	    '(?:a|b)(?:c|d)' => '[ab][cd]', '(?:b|)' => '(?:b|)',
	    '\\0' => '.', 'a\\0\\b' => '(?i:a\\0\\b)', 'a' => 'a(?:b)?',
	    'a(?:b+)?cd' => 'a(?:b+)?c', '(?:a|b)?' => '(?:a|b)?',
	    '(?:ab|cd)+' => '\\w', '[[:digit:]]' => '\\d',
	    '\\d' => '[[:digit:]]', '[[:digit:][:alpha:]]' => '[[:alnum:]]',
	    '[[:alnum:]]' => '[[:digit:][:alpha:]]',
	    '[^[:digit:][:alpha:]]' => '[^[:alnum:]]',
	    '[[:digit:][:alpha:]]' => '[[:alpha:][:digit:]]',
	    '[[:alpha:][:digit:]]' => '[[:digit:][:alpha:]]',
	    '[[:lower:]]' => '[[:alpha:]]', '[[:upper:]]' => '[[:alpha:]]',
	    '[0-9a-f]' => '[[:xdigit:]]',
	    '\\p{Lu}' => '[[:alpha:]]',
	    '[\\w\\-_.]+\\.' => '[-\\w_.]+\\.',
	    '(?i:a(?:b\\s)?\\b)' => '(?i:a(?:b\\s)?\\b)', 'abc' => '(?:|.)',
	    '(?:[\\w\\-_.]+\\.)?' => '(?:[-\\w\\_.]+[.])?',
	    '(?:abc){1,2}' => '\\w', '(?:(?:abc){1,2})+' => '\\w+',
	    '(?:(?:abc){1,2}){4}' => '\\w+',
	    '(?:(?:(?:(?:\\d){1,3})\\.){5}){1,2}' => '(?:(?:(?:(?:\\d){1,3})\\.){4}){1,2}',
	    '(?:(?:(?:(?:\\d){1,3})\\.){5}){1,2}' => '(?:(?:(?:(?:\\d){1,3})\\.){4}){1,}',
	    '(?:(?:(?:(?:\\d){1,3})\\.){5}){1,}' => '(?:(?:(?:(?:\\d){1,3})\\.){4}){1,2}',
	    '(?:(?:(?:(?:\\d){1,3})\\.){5}){3,}' => '(?:(?:(?:(?:\\d){1,3})\\.){4}){1,2}',
	    '(?:(?:(?:(?:d){1,3})\\.){5}){1,2}' => '(?:(?:(?:(?:d){1,3})\\.){4}){1,2}',
	    '(?:(?:(?:(?:d){1,3})\\.){5}){1,2}' => '(?:(?:(?:(?:d){1,3})\\.){4}){1,}',
	    '(?:(?:(?:(?:d){1,3})\\.){5}){1,}' => '(?:(?:(?:(?:d){1,3})\\.){4}){1,2}',
	    '(?:(?:(?:(?:d){1,3})\\.){5}){3,}' => '(?:(?:(?:(?:d){1,3})\\.){4}){1,2}',
	    'abcd' => 'a(?:b(?:c(?:d)?)?)?', 'acd' => 'a(?:b(?:c(?:d)?)?)?',
	    'a*?' => 'a*', 'a*' => 'a*?', 'a+?' => 'a+', 'a+' => 'a+?',
	    'a??' => 'a?', 'a?' => 'a??', 'a??b' => 'a?b', 'a?b' => 'a??b',
	    '(?:ab)??' => '(?:ab)*', '(?:ab)*' => '(?:ab)??',
	    'a.*b' => 'a.*?b', 'a.*?b' => 'a.*b', '(?x:a b)' => 'ab',
	    'ab' => '(?x:a b)', 'Ab' => '(?ix:a B)',
	    "(?x:#comment\nab)" => 'ab', '(?x:[#])' => '#',
	    '(?#before)a' => 'a(?#after)',
	    'a(?#after)' => '(?#before)a', '(?:abc){3}' => 'abcabc',
	    '(?:abc){3}' => 'abcabcabc', '(?:a){2}' => '\\w\\w',
	    '(a)' => '(?:a)', '(?:a)' => '(a)',
	    '(?:b|)a' => '(b|)a', '(b|)a' => '(?:b|)a',
	    'a(?:b|)c' => 'a(b|)c', 'a(b|)c' => 'a(?:b|)c',
	    'a(?:bcd)+' => 'a(bcd)+', 'a(bcd)+' => 'a(?:bcd)+',
	    '(?:^a){1,}' => '(^a){1,}', '(^a){1,}' => '(?:^a){1,}',
	    '(?:abc){1,2}' => '(abc){1,2}', '(abc){1,2}' => '(?:abc){1,2}',
	    '(?:ab)*' => '(ab)*', '(ab)*' => '(?:ab)*',
	    '(?:0+|1)' => '(0+|1)', '(0+|1)' => '(?:0+|1)',
	    '(?:abc)+$' => '(abc)+$', '(abc)+$' => '(?:abc)+$',
	    '(?:abc){3}' => '(abc){3}', '(abc){3}' => '(?:abc){3}',
	    'a(?:b|)' => 'a(b|)', 'a(b|)' => 'a(?:b|)',
	    'a(?:b|)$' => 'a(b|)$', 'a(b|)$' => 'a(?:b|)$',
	    '(?:a\\d){2}' => '(a\\d){2}', '(a\\d){2}' => '(?:a\\d){2}',
	    '(?:aa){2}' => '(aa){2}', '(aa){2}' => '(?:aa){2}',
	    '1(?:aa){2}' => '1(aa){2}', '1(aa){2}' => '1(?:aa){2}',
	    '(?:aa){2}-' => '(aa){2}-', '(aa){2}-' => '(?:aa){2}-',
	    '(?:a|b)(?:c|d)' => '(a|b)(c|d)', '(a|b)(c|d)' => '(?:a|b)(?:c|d)',
	    '(?:(?:a|b)|(?:c|d))' => '((?:a|b)|(?:c|d))',
	    '((?:a|b)|(?:c|d))' => '(?:(?:a|b)|(?:c|d))',
	    '(?:(?:a|b)|(?:c|d))' => '(?:(a|b)|(?:c|d))',
	    '(?:(a|b)|(?:c|d))' => '(?:(?:a|b)|(?:c|d))',
	    '(?:(?:a|b)|(?:c|d))' => '((a|b)|(c|d))',
	    '((a|b)|(c|d))' => '(?:(?:a|b)|(?:c|d))',
	    'a(?:b+)?cd' => 'a(b+)?cd', 'a(b+)?cd' => 'a(?:b+)?cd',
	    '(?:[\\w\\-_.]+\\.)?(?:l(?:so|os)tr)\\.[a-z]{2,}' => '(?:[\\w\\-_.]+\\.)?(?:l(?:so|os)tr)\\.[a-z]{2,}',
	    '(?:busty|enlarge|milf)' => '(?:busty|casino|enlarge|gambling|milf|penis)',
	    '\\barcor\\.de\\b' => 'arcor\\.de',
	    '01-ringe?tones?\\.com' => '01-ringe?tones?[.]com',
	    '\\w(?=\\t)' => '\\w+(?=\\t)', '\\w(?=\\t)c' => '\\w(?=\\s)c',
	    '\\d(?=ab)\\w' => '\\d(?=a).', '^(?=(a|b))' => '(?=[ab])',
	    'foo(?!bar)' => 'foo', 'foo(?=bar)' => 'foo',
	    '^(?!b)' => '^(?!bar)',
	    '\\b(?<=\w)b' => '(?<=\w)b', '\\B(?<=\w)b' => '(?<=\w)b',
	    '(?<!%)%20' => '%20', '(?<!x)%20' => '%20',
	    '(?<!%)%20' => '(?<!%)%20', '(?<!\\d)%20' => '(?<!\\d\\d)%20',
	    '(?<!(?i:\\w))%20' => '(?<![a-f])%20',
	    '(?<!\\w{2})%20' => '(?<![a-f]z)%20',
	    '(?<!((?:a|b)|(?:c|d)))%20' => '%20',
	    '%(?<!((?:a|b)|(?:c|d)))20' => '%20',
	    '%(?<!((?:a|b)|(?:c|d)))20' => '2',
	    '\\d(?<!0)ab' => 'ab',
	    '(?:casino|gambling|porn|\\bsms|milf|busty|prescription|pharmacy|penis|pills|enlarge)[\\w\\-_.]*\\.[a-z]{2,}' => '(?:busty|casino|enlarge|gambling|milf|penis|pharmacy|pills|porn|prescription|\\bsms)[\\w\\-_.]*\\.[a-z]{2,}',
	    '(?i:\\s*(?:very )?urgent\\s+(?:(?:and|&)\\s+)?\\b)' => '(?i:\\s*(?:very )?urgent\\s+(?:(?:and|&)\\s+)?\\b)',
	    '(?i:(?:Re:|\\[.{1,10}\\])?\\s*(?:very )?urgent\\s+(?:(?:and|&)\\s+)?(?:confidential|assistance|business|attention|reply|response|help)\\b)' => '(?i:(?:Re:|\\[.{1,10}\\])?\\s*(?:very )?urgent\\s+(?:(?:and|&)\\s+)?(?:confidential|assistance|business|attention|reply|response|help)\\b)',
	    '^contact \\S+\\@\\S+\\; run by ezmlm$' => '^contact \\S+\\@\\S+; run by ezmlm$',
	    '[\\x00-\\x08\\x0b\\x0c\\x0e-\\x1f\\x7f-\\xff]' => '[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\xff]',
	    '[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\xff]' => '[\\x00-\\x08\\x0b\\x0c\\x0e-\\x1f\\x7f-\\xff]',
	    'tast' => 't.*st', 'tast' => 't.+st', 'tast' => 't.{0,}st',
	    'tast' => 't.{1,}st', 'tast' => 't.{0,2}st',
	    'tast' => 't.{1,3}st', 't.st' => 't.?st',
	    'ast' => '.*st', 'bombast' => 'b.*st',
	    'tast' => 't(?:a|b|c)st',
	    '[^/]*' => '[^/]*', '[^/\\\\]*' => '[^/]*',
	    '.*' => '[^\\n]*', '[^\\n]*' => '.*',
	    '[^a-c]*' => '[^a]*', 'ab' => '(?:(?:)|.)(?:b)',
	    'ab' => '(?:.|(?:))(?:b)'
	   );
# things that should match but it isn''t clear how to make them:
# 'aa*b' => 'ab',
# '(?:aa)+' => 'a{2,}', 'a+a+' => 'a{2,}', 'a(?:b+)?c' => 'ab*c',
# 'taast' => 't.*st'
# '!(?:aa){2}' => '\\baaaa', '(?:aa){2}3' => 'aaaa\\B'
# 'a(?=b)\\w' => 'ab', '^b' => '(?<!a)b'
# '(?:(?:(?:(?:\d){1,3})\\.){4}){1,2}' => '.+',
# '\x{85}' => '\s', \x{0660} => \d
# '.{3}$' => '.$', '.{6}$' => '...$', '(?i:abc){2}' => 'a[b]c', 
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

	    # 20May2006: push causes missing transitivity tests -
	    # that's clearly a bug in the generator below, but it
	    # isn't clear where exactly...
	    unshift @leq, ($rx, $rx);
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
	   '' => 'a', 'a' => 'aa', 'a' => 'b', 'abc' => 'ac', 'abcd' => 'bd',
	   '[ab]' => 'ab', '.' => 'a',	'.' => '[a]',
	   '(?s:.)' => '[^\\n]', '\\d' => '[a]', 'a' => '\\d', 'a' => '\\s',
	   '\\d' => '[23]', '\\d' => '4', '.' => '\\d', '\\s' => 'a',
	   '\\s' => '[ \\t]', '\\s' => ' ', '.' => '\\s', '\\s' => '.',
	   '\\S' => 'a', '.' => '\\S', '\\S' => '\\S\\S', '\\n' => '.',
	   '[\\n]' => '.', '.' => '\\s', '[^0]' => '\\D',
	   '[[:alpha:]]' => '[[:lower:]]', '[[:alpha:]]' => '[[:upper:]]',
	   '[[:digit:]]' => '[[:xdigit:]]', '\\d' => '[0-9]{2}',
	   '[0-9]' => '\\d{2}', '\\s' => '\\s{2}', '\\s' => '[^x]{2}',
	   'y' => '[^x]{2}', 'a' => '\\w{2}', '[a]' => 'a{2}',
	   '\\p{IsLower}' => '\\p{IsUpper}',
	   '[[:alpha:]]' => '\\p{Lu}',
	   '\\d' => '[0-9]', '[^0-9]' => '\\D', # Unicode has numbers beyond ASCII - try e.g. \x{0660}" =~ /\d/
	   '\\w' => '[0-9a-zA-Z_]',
	   '\\D' => '\\W', '(?s:.)' => '.', '[^0]' => '\\w',
	   '(?m:^a)' => '^a', '(?m:^a)' => '(?m:\\Aa)',
	   '(?m:a$)' => 'a$', '(?m:a$)' => '(?m:a\\Z)',
	   '[^\\s]+' => '(?m:^a)', '[^\\w]+' => '(?m:^a)',
	   '(?i:a)' => '\\W', '(?i:0)' => '\\D',
	   'a[b]c' => '(?i:abc){2}', '(?i:abc)' => '([aA][bB][cC]){2}',
	   '(?i:abc)' => '(?i:abc){2}', '(abc)' => '(abc){2}',
	   '([ab])\\1' => '(?:([ab])\\1){2}',
	   'a[bc]de' => '[bc]e', 'a' => '^a', '[a-z]' => '^a',
	   'a*' => 'a', 'a*' => 'a+', 'xa{1,}y' => 'xay',
	   'a+' => 'a{2,}', 'ab+c' => 'abc', 'a+' => 'aaa',
	   'ab+c' => 'a+bc',
	   '(?:^a)*' => '^a', 'ab+c' => 'ab{2,}c', 'ab{1,}c' => 'abc',
	   '^-' => '\\b', '[a ]' => '\\b', 'a' => '\\ba',
	   '\\B' => '\\b', '\\b' => '\\B', '\\b[a ]' => '(?:\\b[a ]){2}',
	   '\\B[a ]' => '(?:\\B[a ]){2}', '\\w+' => 'abc',
	   '\\w{3,}' => 'abc', '\\d{1,}' => '0+', 'a+' => '\\d+',
	   'a+' => 'b{1,}', 'abc' => 'a*bd', '(?i:a)' => 'a',
	   'a(?:b|)c' => 'ac', '[abc]' => 'a|b', 'a|b' => 'a',
	   '.$' => '.{3}$', '...$' => '.{6}$', '^a' => 'a$', 'a$' => '^a',
	   'a*' => 'a$',
	   'a{2}' => 'ab', 'ab' => 'a{2}', '\\w' => '.{2}',
	   '\\S' => '.{2}', '\\d' => '.{2}', '.' => '(?s:.){2}',
	   '(?s:.)' => '(?s:.){2}', '[a-z]' => '(?s:.){2}',
	   '\\w' => '(?s:.){2}', '\\W' => '(?s:.){2}',
	   '\\s' => '(?s:.){2}', '\\S' => '(?s:.){2}',
	   '\\d' => '(?s:.){2}', '\\D' => '(?s:.){2}',
	   'a' => '(?s:.){2}', '(?i:a)' => '(?s:.){2}',
	   '\\w' => '\\w{2}', '\\w' => '\\S{2}', '\\d' => '\\w{2}',
	   '\\W' => '\\W{2}', '\\s' => '\\W{2}', '\\S' => '\\S{2}',
	   '\\d' => '\\S{2}', '\\d' => '\\d{2}', '\\W' => '\\D{2}',
	   '\\s' => '\\D{2}', '\\D' => '\\D{2}',
	   '1(?:aa){2}' => '\\baaaa', '(?:aa){2}!' => 'aaaa\\B',
	   '(?:(?:(?:(?:\\d){1,3})\\.){4}){1,2}' => '(?:(?:(?:(?:\\d){1,3})\\.){5}){1,2}',
	    '(?:(?:(?:(?:\\d){1,3})\\.){5}){1,2}' => '(?:(?:(?:(?:\\d){1,3})\\.){4}){3,}',
	   '(?:busty|casino|enlarge|gambling|milf|penis)' => '(?:busty|enlarge|milf)',
	   '(?:[\\w\\-_.]+\\.)?(?:l(?:so|os)tr)\\.[a-z]{2,}' => '(?:[\\w\\-_.]+\\.)?(?:l(?:so|os)tr)\\. ',
	   't.st' => 'ta*st',
	   '(?=[ab])' => '^(?=(a|b))', '^(?=(a|b)).' => '(?=[ab])..',
	   'foo' => 'foo(?!bar)', '^(?!bar)' => '^(?!b)',
	   '(?=bar)b' => '(?!bar)b', '(?!bar)b' => '(?=bar)b',
	   '%20' => '(?<!%)%20', '%20' => '(?<!x)%20',
	   '(?<!((?:a|b)|(?:c|d)))%20' => '%21',
	   '(?<!\\d\\d)%20' => '(?<!\\d)%20', '(?<!\\w)b' => '(?<=\\w)b',
	   '(?<=\\w)b' => '(?<!\\w)b',
	   '[^/]*' => '[^/\\\\]*', '(?ix:a B)' => 'Ab',
	   'x(?:ab)*y' => 'x(?:ab)??y', '\x{263a}+' => ' +',
	   ' +' => '[\x{263a}]+',
	   '[^a]*' => '[^a-c]*', '(?:(?:)|.)(?:b)' => 'ab',
	   '(?:.|(?:))(?:b)' => 'ab'
	  );

    @invalid = ( 'a' => '[a', 'a{2,1}' => 'a' );
}

use Test::More tests => (scalar(@leq) / 2) + (scalar(@nc) / 2) + (scalar(@invalid) / 2);

$i = 0;
while ($i < scalar(@leq)) {
    # warn 'testing ' . $leq[$i] . ' <= ' . $leq[$i + 1] . "\n";
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
    ok($@, $invalid[$i] . ' vs. ' . $invalid[$i + 1]);
    $i += 2;
}
