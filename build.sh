g++ plua.cpp -fPIC -shared -o libplua.so  -I../LuaJIT-2.0.5/src -L./ -lluajit -lgvc -g -Wl,-rpath=./
# g++ plua.cpp -fPIC -shared -o libplua.so  -I../lua-5.3.5/src  ../lua-5.3.5/src/liblua.a -lgvc
# g++ plua.cpp -fPIC -shared -o libplua.so  -L../lua-5.3.5/src -llua -lgvc
# g++ plua.cpp -fPIC -shared -o libplua.so -L./ -llua -lgvc -Wl,-rpath=./
