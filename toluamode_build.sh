# g++ plua.cpp -fPIC -shared -o libplua.so  -I../../work/ATBattle/include/tolua_runtime/luajit-2.1/src/ -L../../work/ATBattle/include/tolua_runtime/  -lluajit -lgvc -g -Wl,-rpath=../../work/ATBattle/include/tolua_runtime/
#g++ -o main main.c -I../LuaJIT-2.0.5/src -L. -lluajit -lm -ldl -Wl,-rpath=./

g++ plua.cpp -fPIC -shared -o libplua.so  -I../tolua_runtime/luajit-2.1/src/ -L../../libs/linux/Release/ -lluajit -lgvc -g -std=c++11 -Wl,-rpath=../../work/ATBattle/libs/linux/Release/
cp libplua.so ../../libs/linux/Release/
