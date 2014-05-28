mergesort
=========

Merge sort correctness proof in Agda

We present a version of merge sort, fully certified, in Agda. It features: syntactic warrant of termination (i.e. no need of explicit termination proof), no proof cost to ensure the output is sorted, and almost free proof that the output is a permutation of the input.

## Important source files ##
- **Nat.agda** - Section 2 - Natural numbers with an upper bound
- **Snat.agda** - Section 2 - Agda's Sized Types introduction
- **MergeSort.agda** - Section 2 - Merge sort termination check with Sized Types
- **MergeSort3.agda** - Section 3 - Merge sort proof of sorted specification
- **Permutation.agda** - Section 3 - Permutation related stuff
- **MergeSort4.agda** - Section 3 - Merge sort complete proof of correctness of sorting and permutation specifications

## Agda's complier verion ##
Agda version 2.3.2.2

## Agda's library verion ##
Version 0.7 of the standard library