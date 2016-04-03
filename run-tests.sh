#!/bin/bash

f2b="./formula-2-bdd"
tests_dir="tests"

mkdir -p tmp && rm -rf tmp/*
tests=`find $tests_dir | egrep "\.in$" | xargs -n1 basename | sed -r "s/\.in$//g" | sort`

compare_test_result() {
	diff -u "$tests_dir/$1.in" "tmp/$1.in.out" >/dev/null 2>&1
	if [ $? -ne 0 ]; then
		return -1
	fi

	diff -u "$tests_dir/$1.tab" "tmp/$1.tab.out" >/dev/null 2>&1
	if [ $? -ne 0 ]; then
		return -1
	fi

	diff -u <(echo `cat "$tests_dir/$1.bdd" | sort`) <(echo `cat "tmp/$1.bdd.out" | sort`)
	if [ $? -ne 0 ]; then
		return -1
	fi

	diff -u <(cat "$tests_dir/$1.robdd" | sort) <(cat "tmp/$1.robdd.out" | sort)
	if [ $? -ne 0 ]; then
		return -1
	fi

	return 0
}

run_test() {
	[[ "$1" =~ err_(.*) ]] && error_test=1 || error_test=0

	$f2b -i "$tests_dir/$1.in" > tmp/"$test_name".in.out 2>/dev/null
	if [ $error_test -eq 1 ]; then
		if [ $? -ne 0 ]; then
			return 0
		else
			return -1
		fi
	fi

	$f2b -t "$tests_dir/$1.in" > tmp/"$test_name".tab.out 2>/dev/null
	$f2b -b "$tests_dir/$1.in" > tmp/"$test_name".bdd.out 2>/dev/null
	$f2b -r "$tests_dir/$1.in" > tmp/"$test_name".robdd.out 2>/dev/null

	compare_test_result $test_name
	return $?
}

print_test_result() {
	if [ -t 1 ]; then
		green_color="\e[1;32m"
		red_color="\e[1;31m"
		no_color="\e[0m"
	else
		green_color=""
		red_color=""
		no_color=""
	fi

	if [ $2 -eq 0 ]; then
		printf "%-60s [ %b%s%b ]\n" $1 $green_color "PASS" $no_color
	else
		printf "%-60s [ %b%s%b ]\n" $1 $red_color "FAIL" $no_color
	fi
}

for test_name in $tests; do
	run_test $test_name
	print_test_result $test_name $?
done
