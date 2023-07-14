# abc
git clone https://github.com/berkeley-abc/abc
cd abc

# switch to stable commit(581c58b)
git reset 581c58b 

# modify abc src content
sed -e '/#include <cmath>/ a#include <stdexcept>' src/aig/gia/giaNewBdd.h > src/aig/gia/tempBdd.h
sed -e '/#include <bitset>/ a#include <stdexcept>' src/aig/gia/giaNewTt.h > src/aig/gia/tempTt.h
rm -rf src/aig/gia/giaNewBdd.h; rm -rf src/aig/gia/giaNewTt.h;
mv src/aig/gia/tempBdd.h src/aig/gia/giaNewBdd.h; mv src/aig/gia/tempTt.h src/aig/gia/giaNewTt.h;

rm -rf src/base/abci/tempPrint.c
sed -e '1608 a \    FILE *file;\n    file = fopen("support", "a");' src/base/abci/abcPrint.c > src/base/abci/tempPrint.c
sed -e '1620 a \        Abc_NtkForEachCi( pNtk, pObj, k )\n            fprintf(file, "%d", pObj->fMarkA );' src/base/abci/tempPrint.c > src/base/abci/abcPrint.c
sed -e '1622 a \        fprintf(file, "\\n" );' src/base/abci/abcPrint.c > src/base/abci/tempPrint.c
sed -e '1628 a \    fclose(file);' src/base/abci/tempPrint.c > src/base/abci/abcPrint.c

# make "abc" static library
make libabc.a

# copy "libabc.a" static library to /lib
ln -s ../lib/libabc.a ../abc/libabc.a;

# make bmatch
cd ..; make;

