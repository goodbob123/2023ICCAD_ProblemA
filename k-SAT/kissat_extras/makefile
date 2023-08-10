all:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build"
kissat:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" kissat
tissat:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" tissat
clean:
	rm -f "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras"/makefile
	-$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" clean
	rm -rf "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build"
coverage:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" coverage
headers:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" headers
indent:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" indent
test:
	$(MAKE) -C "/home/wish/2023ICCAD_ProblemA/k-SAT/kissat_extras/build" test
.PHONY: all clean coverage indent kissat test tissat
