include $(top_srcdir)/config/Makefile.for.ROSE.includes.and.libs

TEST_PATH=$(top_srcdir)/projects/FaultToleranceFramework/test
INCLUDES = $(ROSE_INCLUDES) -I$(top_srcdir)/projects/FaultToleranceFramework/include
LDFLAGS = -L$(top_builddir)/projects/FaultToleranceFramework/src
LDADD = $(ROSE_LIBS) -lroseft

bin_PROGRAMS = ft_transVOTE.exe ft_transVOTEMEDIAN.exe ft_transVOTEMEAN.exe ft_transVOTEEXACT.exe ft_transVOTEEXACT_FAST.exe

ft_transVOTE_exe_SOURCES = $(TEST_PATH)/ft_trans_Voting.C
ft_transVOTEMEAN_exe_SOURCES = $(TEST_PATH)/ft_trans_Voting_Mean.C
ft_transVOTEMEDIAN_exe_SOURCES = $(TEST_PATH)/ft_trans_Voting_Median.C
ft_transVOTEEXACT_exe_SOURCES = $(TEST_PATH)/ft_trans_Voting_Exact.C
ft_transVOTEEXACT_FAST_exe_SOURCES = $(TEST_PATH)/ft_trans_Voting_Exact_AssumeMajElem.C

TRANSFORM_TESTCODES_REQUIRED_TO_PASS = \
				fttest1_C.C \
				fttest4_C.C \
				ll_kernel1.C \
				ll_kernel4.C \
				ll_kernel5.C \
				ll_kernel11.C

TRANSFORM_TESTCODE_CURRENTLY_FAILING = \
				fttest2_C.C \
				fttest3_C.C \
				fttest1_Cxx.C \
				fttest1_F.f \
				fttest1_F.f90 \
				fttest2_Cxx.C

TRANSFORM_ALL_TESTCODES = \
	$(TRANSFORM_TESTCODES_REQUIRED_TO_PASS) \
	$(TRANSFORM_TESTCODE_CURRENTLY_FAILING)

TRANSFORM_TRANSLATOR_PATH = $(top_builddir)/projects/FaultToleranceFramework/test
TRANSFORM_TEST_PATH = $(TEST_PATH)/Transform
TRANSFORM_OUT_PATH = $(top_builddir)/projects/FaultToleranceFramework/test/Transform

ROSE_COMPILE_FLAGS=

$(TRANSFORM_TRANSLATOR):
	@$(MAKE) -C $(top_builddir)/projects/FaultToleranceFramework/src

TRANSFORM_MAKE = ${TRANSFORM_TESTCODES_REQUIRED_TO_PASS:.C=}
$(TRANSFORM_MAKE): $(TRANSFORM_TRANSLATOR)
#...Compile testcase in all configurations...
		$(TRANSFORM_TRANSLATOR_PATH)/ft_transVOTE $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$@.C -rose:output $(TRANSFORM_OUT_PATH)/$@_VOTE.out.C
		$(TRANSFORM_TRANSLATOR_PATH)/ft_transVOTEMEAN $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$@.C -rose:output $(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.out.C
		$(TRANSFORM_TRANSLATOR_PATH)/ft_transVOTEMEDIAN $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$@.C -rose:output $(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.out.C
		$(TRANSFORM_TRANSLATOR_PATH)/ft_transVOTEEXACT $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$@.C -rose:output $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.out.C
		$(TRANSFORM_TRANSLATOR_PATH)/ft_transVOTEEXACT_FAST $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$@.C -rose:output $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.out.C
#... Link, execute and compare results (if there's any precomputed output) ....
#		if [ -a $(TRANSFORM_TEST_PATH)/$@.output ] then
#			$(CXX) $(TRANSFORM_OUT_PATH)/$@_VOTE.out.C -o $(TRANSFORM_OUT_PATH)/$@_VOTE.out
#			$(TRANSFORM_OUT_PATH)/$@_VOTE.out > $(TRANSFORM_OUT_PATH)/$@_VOTE.output
#			if [[ $$(diff -r $(TRANSFORM_OUT_PATH)/$@_VOTE.output $(TRANSFORM_TEST_PATH)/$@.output ) != "" ]]; then echo "Files differ; test falied"; exit 1; fi
#			$(CXX) $(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.out.C -o $(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.out
#			$(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.out > $(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.output
#			if [[ $$(diff -r $(TRANSFORM_OUT_PATH)/$@_VOTE_MEAN.output $(TRANSFORM_TEST_PATH)/$@.output ) != "" ]]; then echo "Files differ; test falied"; exit 1; fi
#			$(CXX) $(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.out.C -o $(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.out
#			$(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.out > $(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.output
#			if [[ $$(diff -r $(TRANSFORM_OUT_PATH)/$@_VOTE_MEDIAN.output $(TRANSFORM_TEST_PATH)/$@.output ) != "" ]]; then echo "Files differ; test falied"; exit 1; fi
#			$(CXX) $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.out.C -o $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.out
#			$(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.out > $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.output
#			if [[ $$(diff -r $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT.output $(TRANSFORM_TEST_PATH)/$@.output ) != "" ]]; then echo "Files differ; test falied"; exit 1; fi
#			$(CXX) $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.out.C -o $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.out
#			$(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.out > $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.output
#			if [[ $$(diff -r $(TRANSFORM_OUT_PATH)/$@_VOTE_EXACT_FAST.output $(TRANSFORM_TEST_PATH)/$@.output ) != "" ]]; then echo "Files differ; test falied"; exit 1; fi
#		fi	

TEST_TRANSLATOR=ft_transVOTE
TEST_SOURCE=fttest2_C.C
debug:
	libtool --mode=execute gdb --args $(TRANSFORM_TRANSLATOR_PATH)/$(TEST_TRANSLATOR) $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$(TEST_SOURCE) -rose:output $(TRANSFORM_OUT_PATH)/fttest_debug.out
mem_debug:
	libtool --mode=execute valgrind --tool=memcheck $(TRANSFORM_TRANSLATOR_PATH)/$(TEST_TRANSLATOR) $(ROSE_COMPILE_FLAGS) -c $(TRANSFORM_TEST_PATH)/$(TEST_SOURCE) -rose:output $(TRANSFORM_OUT_PATH)/fttest_mem_debug.out

check-local:
	@echo "Test for FTTransform"
	@rm -rf Transform/*.out
	@$(MAKE) $(TRANSFORM_MAKE)
	@echo "*****************************************************************************************************************"
	@echo "****** ROSE/projects/FfaultToleranceFramework/test: make check rule complete (terminated normally) **************"
	@echo "*****************************************************************************************************************"

EXTRA_DIST = 

SUBDIRS = Analysis Transform

clean-local:
	rm -f *.o *.out
