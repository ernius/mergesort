mergesort 
=========

Case of (Quite) Painless Dependently Typed Programming: Fully Certified Merge Sort in Agda
==========================================================================================

Merge sort correctness proof in Agda

We present a version of merge sort, fully certified, in Agda. It features: syntactic warrant of termination (i.e. no need of explicit termination proof), no proof cost to ensure the output is sorted, and almost free proof that the output is a permutation of the input.

## Documentation files ##
- **sblp2014_submission_31.pdf** - Submited paper to [Lecture Notes in Computer Science, Springer](http://link.springer.com/chapter/10.1007/978-3-319-11863-5_5)

## Source files ##
- **Nat.agda** - Section 2 - Natural numbers with an upper bound
- **Snat.agda** - Section 2 - Agda's Sized Types introduction
- **MergeSort.agda** - Section 2 - Merge sort with Sized Types's termination check
- **MergeSort3.agda** - Section 3 - Merge sort algorithm's correctness proof against list's sort specification
- **Permutation.agda** - Section 3 - Permutation related stuff
- **MergeSort4.agda** - Section 3 - Merge sort algorithm's correctness proofagainst list's sort and permutation specifications
- **MergeSort3Perm.agda** - Section 3 - Merge sort algorithm's correctness proof against permutation specifications, not embedding algorhitm's code within the proof as in MergeSort4 file

## Agda's complier version ##

Agda version 2.3.2.2
Standard Library version 0.7

## Build status in Travis CI : [![Build Status](https://travis-ci.org/ernius/mergesort.svg?branch=master)](https://travis-ci.org/ernius/mergesort) ##


