# abc
git clone https://github.com/berkeley-abc/abc
cd abc

# switch to stable commit(581c58b)
git reset 581c58b 
git clean -f
git checkout .

# modify abc src content
#sed -e '/#include <cmath>/ a#include <stdexcept>' src/aig/gia/giaNewBdd.h > src/aig/gia/tempBdd.h
#sed -e '/#include <bitset>/ a#include <stdexcept>' src/aig/gia/giaNewTt.h > src/aig/gia/tempTt.h
#rm -rf src/aig/gia/giaNewBdd.h; rm -rf src/aig/gia/giaNewTt.h;
#mv src/aig/gia/tempBdd.h src/aig/gia/giaNewBdd.h; mv src/aig/gia/tempTt.h src/aig/gia/giaNewTt.h;

rm -rf src/base/abci/tempPrint.c
sed -e '1608 a \    FILE *file;\n    file = fopen("support", "a");' src/base/abci/abcPrint.c > src/base/abci/tempPrint.c
sed -e '1618,1619 c \        Abc_NtkForEachCi( pNtk, pObj, k )\n            fprintf(file, "%d", pObj->fMarkA );' src/base/abci/tempPrint.c > src/base/abci/abcPrint.c
sed -e '1620 c \        fprintf(file, "\\n" );' src/base/abci/abcPrint.c > src/base/abci/tempPrint.c
sed -e '1625 a \    fclose(file);' src/base/abci/tempPrint.c > src/base/abci/abcPrint.c

rm -rf src/base/abc/tempDfs.c
sed -e '900 c \        if ( Abc_ObjIsCo(ppNodes[i]) && ppNodes[i]->vFanins.pArray[0] != 0 )' src/base/abc/abcDfs.c > src/base/abc/tempDfs.c
rm -rf src/base/abc/abcDfs.c; mv src/base/abc/tempDfs.c src/base/abc/abcDfs.c;

# make "abc" static library
make libabc.a

# copy "libabc.a" static library to /lib
ln -s ../abc/libabc.a ../lib/libabc.a;

# make bmatch
cd ..; 
make;

