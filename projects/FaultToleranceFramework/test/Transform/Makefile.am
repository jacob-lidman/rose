include $(top_srcdir)/config/Makefile.for.ROSE.includes.and.libs

TEST_PATH = $(top_srcdir)/projects/FaultToleranceFramework/test/Transform

TEST_CODES = $(TEST_PATH)/fttest1_C.C \
	$(TEST_PATH)/fttest1_Cxx.C \
	$(TEST_PATH)/fttest1_F.f \
	$(TEST_PATH)/fttest1_F.f90 \
	$(TEST_PATH)/fttest2_C.C \
	$(TEST_PATH)/fttest2_Cxx.C \
	$(TEST_PATH)/fttest3_C.C \
	$(TEST_PATH)/fttest4_C.C \
	$(TEST_PATH)/testcase.C \
	$(TEST_PATH)/ll_kernel1.C \
	$(TEST_PATH)/ll_kernel4.C \
	$(TEST_PATH)/ll_kernel5.C \
	$(TEST_PATH)/ll_kernel11.C

CORRECT_OUTPUT = $(TEST_PATH)/fttest1_C.output \
	$(TEST_PATH)/fttest2_C.output \
	$(TEST_PATH)/fttest4_C.output

EXTRA_DIST = $(TEST_CODES) $(CORRECT_OUTPUT)
