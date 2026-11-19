ROCQ ?= rocq

.PHONY: all
all:
	$(ROCQ) compile -Q theories SortingExample theories/SortSpec.v
	$(ROCQ) compile -Q theories SortingExample theories/MergeSort.v
	$(ROCQ) compile -Q theories SortingExample theories/MergeSortCorrect.v
