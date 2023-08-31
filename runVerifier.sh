#!/bin/bash
echo " ------------ Check Case ${1} ------------"
if [ "$1" == "" ]; then
    echo "please enter the case numbers e.g. 01,02,10..."
elif [ "$1" == "-h" ]; then
    echo "bash runVerifier.sh <case number (01,02,10...)>  [match (default=match)]"
else

    if [ "$2" == "" ]; then
        match="match"
    else 
        match=$2
    fi
echo "The match file name : $match" 

# process matchfile
sed -i 's/<//g' $match
sed -i 's/>//g' $match

# run verifier
cmd="cirver CAD_testdata/case${1}/circuit_1.v CAD_testdata/case${1}/circuit_2.v $match  \nquit -f"
file_path="dofile"
rm $file_path
echo -e "$cmd" >> "$file_path"

./bmatch_v2 -f dofile


fi
