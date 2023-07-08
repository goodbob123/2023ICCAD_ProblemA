# abc
git clone https://github.com/berkeley-abc/abc
cd abc

# switch to stable commit(581c58b)
git reset 581c58b 

# modify abc src content
#giaNewBdd.h
#giaNewTt.h
#<stdexcept>
sed -e '/#include <cmath>/ a#include <stdexcept>' src/aig/gia/giaNewBdd.h > src/aig/gia/tempBdd.h
sed -e '/#include <bitset>/ a#include <stdexcept>' src/aig/gia/giaNewTt.h > src/aig/gia/tempTt.h
rm -rf src/aig/gia/giaNewBdd.h; rm -rf src/aig/gia/giaNewTt.h;
mv src/aig/gia/tempBdd.h src/aig/gia/giaNewBdd.h; mv src/aig/gia/tempBdd.h src/aig/gia/giaNewBdd.h;

# make "abc" static library
make libabc.a

# copy "libabc.a" static library to /lib
mv libabc.a ../lib;

# make bmatch
cd ..; make;

