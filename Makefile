SRCPKGS  = util cmd mod abc bdd itp ntk sim vrf ext prove bmatch
LIBPKGS  = util cmd mod abc bdd itp ntk sim vrf prove bmatch

MAIN     = main

EXTLIBS	 = -lm -lz -lreadline -ltermcap -ldl -lstdc++ -ltcl -lffi -lgmp
SRCLIBS  = $(addprefix -l, $(LIBPKGS)) $(addprefix -l, $(ENGPKGS))


#ENGPKGS	 += quteRTL
ENGPKGS	 += boolector
ENGPKGS	 += lgl
ENGPKGS	 += btor2parser
#ENGPKGS	 += minisat
ENGPKGS	 += abcc
ENGPKGS	 += yosys

ENGSSRC	 = eng

EXEC     = ./bin/gv
.PHONY : all debug

all : EXEC     = ./bin/gv
debug : EXEC     = gv.debug

all:  DEBUG_FLAG =
debug:DEBUG_FLAG = -DGV_DEBUG

LIB	     = libgv.a


all debug:	srcLib ./bin/parser ./bin/aig_map ./bin/satTest
	@echo "Checking $(MAIN)..."
	@cd src/$(MAIN); make --no-print-directory EXTLIB="$(SRCLIBS) $(EXTLIBS)" EXEC=$(EXEC); cd ../.. ;

srcLib:	engLib 
	@cd include; ln -fs ../src/*/*.h ./;
	@for pkg in $(SRCPKGS); \
	do \
		echo "Checking $$pkg..."; \
		cd src/$$pkg; make --no-print-directory DEBUG_FLAG=$(DEBUG_FLAG) PKGNAME=$$pkg || exit;  \
		cd ../.. ; \
	done

engLib:	
	@for pkg in $(ENGPKGS);	\
	do \
		cd include ; ln -fs ../src/$(ENGSSRC)/$$pkg/* .; cd .. ; \
		cd lib ; ln -fs ../src/$(ENGSSRC)/$$pkg/*.a .; ln -fs ../src/$(ENGSSRC)/$$pkg/*.so .; cd .. ; \
	done
	@rm -f include/*.a

main:
	@echo "Checking $(MAIN)..."
	@cd src/$(MAIN); \
		make --no-print-directory EXTLIB="$(SRCLIBS) $(EXTLIBS)" EXEC=$(EXEC);
	@ln -fs bin/$(EXEC) .
#	@strip bin/$(EXEC)

clean:	
	@for pkg in $(SRCPKGS); \
	do \
		echo "Cleaning $$pkg..."; \
		cd src/$$pkg; make --no-print-directory PKGNAME=$$pkg clean; \
		cd ../.. ; \
	done
	@echo "Cleaning $(MAIN)..."
	@cd src/$(MAIN); make --no-print-directory clean
	@echo "Removing $(EXEC)..."
	@rm -f $(EXEC) 
	@rm -f ./bin/parser
	@rm -f ./bin/aig_map
	@rm -f ./bin/satTest
	@rm -f ./SAT/test/*.o satTest tags

ctags:	
	@rm -f src/tags
	@for pkg in $(SRCPKGS); \
	do \
		echo "Tagging $$pkg..."; \
		cd src; ctags -a $$pkg/*.cpp $$pkg/*.h; cd ..; \
	done
	@echo "Tagging $(MAIN)..."
	cd src; ctags -a $(MAIN)/*.cpp
	@echo "Tagging $(GUI)..."
	cd src; ctags -a $(GUI)/*.cpp

rmdep:	
	@for pkg in $(SRCPKGS); \
	do \
		rm src/$$pkg/.*.mak; \
	done
	@rm src/main/.*.mak;

linux18 linux16 mac:
	@for pkg in $(REFPKGS); \
	do \
	        cd lib; ln -sf lib$$pkg-$@.a lib$$pkg.a; cd ../..; \
	done
	@cd ref; ln -sf $(EXEC)-$@ $(EXEC);

./bin/parser: ./parser/parser.cpp
	g++ ./parser/parser.cpp -O3 -o ./bin/parser

./bin/aig_map: ./parser/aig_map.cpp
	g++ ./parser/aig_map.cpp -O3 -o ./bin/aig_map

./bin/satTest: ./SAT/test/File.o ./SAT/test/Proof.o ./SAT/test/Solver.o ./SAT/test/satTest.o
	g++ -O3 -std=c++20 -g ./SAT/test/File.o ./SAT/test/Proof.o ./SAT/test/Solver.o ./SAT/test/satTest.o -o ./bin/satTest
	rm -rf *.o

./SAT/test/File.o: ./SAT/test/File.cpp
	g++ -c -O3 -std=c++20 -g ./SAT/test/File.cpp -o ./SAT/test/File.o

./SAT/test/Proof.o: ./SAT/test/Proof.cpp
	g++ -c -O3 -std=c++20 -g ./SAT/test/Proof.cpp -o ./SAT/test/Proof.o

./SAT/test/Solve.o: ./SAT/test/Solver.cpp
	g++ -c -O3 -std=c++20 -g ./SAT/test/Solver.cpp -o ./SAT/test/Solver.o

./SAT/test/satTest.o: ./SAT/test/satTest.cpp
	g++ -c -O3 -std=c++20 -g ./SAT/test/satTest.cpp -o ./SAT/test/satTest.o
	