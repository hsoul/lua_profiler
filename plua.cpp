#include <string>
#include <list>
#include <vector>
#include <map>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <string>
#include <cstdlib>
#include <cstring>
#include <typeinfo>
#include <stdio.h>
#include <time.h>
#include <stdarg.h>
#include <assert.h>
#include <math.h>
#include <sys/time.h>
#include <signal.h>
#include <unistd.h>
#include <errno.h>
#include <unordered_map>
#include <fcntl.h>
#include <sstream>
#include <algorithm>
#include <vector>
#include <unordered_set>
#include <set>
#include <graphviz/gvc.h>

extern "C" {
#include "lua.h"
#include "lualib.h"
#include "lauxlib.h"
}

int open_debug = 0;
int g_samplecount;
std::string g_filename;
lua_State *gL;
int grunning = 0;

#define LLOG(...) if (open_debug) {llog("[DEBUG] ", __FILE__, __FUNCTION__, __LINE__, __VA_ARGS__);}
#define LERR(...) if (open_debug) {llog("[ERROR] ", __FILE__, __FUNCTION__, __LINE__, __VA_ARGS__);}

void llog(const char* header, const char* file, const char* func, int pos, const char* fmt, ...) 
{
    FILE* pLog = NULL;
    time_t clock1;
    struct tm *tptr;
    va_list ap;

    pLog = fopen("plua.log", "a+");
    if (pLog == NULL) {
        return;
    }

    clock1 = time(0);
    tptr = localtime(&clock1);

    struct timeval tv;
    gettimeofday(&tv, NULL);

    fprintf(pLog, "===========================[%d.%d.%d, %d.%d.%d %llu]%s:%d,%s:===========================\n%s",
            tptr->tm_year + 1990, tptr->tm_mon + 1,
            tptr->tm_mday, tptr->tm_hour, tptr->tm_min,
            tptr->tm_sec, (long long) ((tv.tv_sec) * 1000 + (tv.tv_usec) / 1000), file, pos, func, header);

    va_start(ap, fmt);
    vfprintf(pLog, fmt, ap);
    fprintf(pLog, "\n\n");
    va_end(ap);

    va_start(ap, fmt);
    vprintf(fmt, ap);
    printf("\n\n");
    va_end(ap);

    fclose(pLog);
}

static const int MAX_FUNC_NAME_SIZE = 127;

/////////////////////////////copy from lua start///////////////////////////////////////////////

/*
** search for 'objidx' in table at index -1.
** return 1 + string at top if find a good name.
*/
static int findfield(lua_State *L, int objidx, int level) // obj_idx 正数， level 遍历层级， if find object push object name onto stack
{
    if (level == 0 || !lua_istable(L, -1))
        return 0;  /* not found */
    lua_pushnil(L);  /* start 'next' loop */
    while (lua_next(L, -2)) /* for each pair in table */
	{  
        if (lua_type(L, -2) == LUA_TSTRING) /* ignore non-string keys */
		{  
            if (lua_rawequal(L, objidx, -1)) /* found object? */
			{  
                lua_pop(L, 1);  /* remove value (but keep name) */
                return 1;
            } 
			else if (findfield(L, objidx, level - 1)) /* try recursively */
			{  
                lua_remove(L, -2);  /* remove table (but keep name) */
                lua_pushliteral(L, ".");
                lua_insert(L, -2);  /* place '.' between the two names */
                lua_concat(L, 3);
                return 1;
            }
        }
        lua_pop(L, 1);  /* remove value */
    }
    return 0;  /* not found */
}

/*
** Search for a name for a function in all loaded modules
*/
static int pushglobalfuncname(lua_State *L, lua_Debug *ar) 
{
    int top = lua_gettop(L);
    lua_getinfo(L, "f", ar);  /* push function */
    lua_getfield(L, LUA_REGISTRYINDEX, "_LOADED");
    if (findfield(L, top + 1, 6)) 
	{
        const char *name = lua_tostring(L, -1);
        if (strncmp(name, "_G.", 3) == 0)  /* name start with '_G.'? */
		{ 
            lua_pushstring(L, name + 3);  /* push name without prefix */
            lua_remove(L, -2);  /* remove original name */
        }
#if LUA_VERSION_NUM > 502
		lua_copy(L, -1, top + 1);  /* move name to proper place */
		lua_pop(L, 2);  /* remove pushed values */
#else
		lua_replace(L, top + 1);
		lua_settop(L, top + 1);
#endif
        return 1;
    } else {
        lua_settop(L, top);  /* remove function and global table */
        return 0;
    }
}


static void pushfuncname(lua_State* L, lua_Debug* ar) 
{
	if (*ar->namewhat != '\0')  /* is there a name from code? */
        lua_pushfstring(L, "%s '%s'", ar->namewhat, ar->name);  /* use it */
	else if (pushglobalfuncname(L, ar)) /* try first a global name */
	{  
		lua_pushfstring(L, "function '%s'", lua_tostring(L, -1));
		lua_remove(L, -2);  /* remove name */
		printf("######### global func name\n");
	}
    else if (*ar->what == 'm')  /* main? */
        lua_pushliteral(L, "main chunk");
    else if (*ar->what != 'C')  /* for Lua functions, use <file:line> */
        lua_pushfstring(L, "function <%s:%d>", ar->short_src, ar->linedefined);
    else  /* nothing left... */
        lua_pushliteral(L, "?");
}


static int lastlevel(lua_State* L) // 或取最顶层堆栈 index
{
    lua_Debug ar;
    int li = 1, le = 1;
    /* find an upper bound */
    while (lua_getstack(L, le, &ar))
	{
        li = le;
        le *= 2;
    }
    /* do a binary search */
    while (li < le)
	{
        int m = (li + le) / 2;
        if (lua_getstack(L, m, &ar)) li = m + 1;
        else le = m;
    }
    return le - 1;
}


/////////////////////////////copy from lua end///////////////////////////////////////////////

std::unordered_map<std::string, int> g_String2Id;
std::unordered_map<int, std::string> g_Id2String;

static const int VALID_MIN_ID = 3;

static const int MAX_STACK_SIZE = 64;
static const int MAX_CALL_STACK_SIZE = 4;
static const int MAX_BUCKET_SIZE = 1 << 10;
static const int MAX_CALL_STACK_SAVE_SIZE = 1 << 18;

struct CallStack 
{
    int count;
    int depth;
    int stack[MAX_STACK_SIZE];
};

struct Bucket 
{
    CallStack cs[MAX_CALL_STACK_SIZE];
};

struct ProfileData 
{
    Bucket bucket[MAX_BUCKET_SIZE];
    int total;
};

int gfd;

ProfileData g_ProfileData;
CallStack gCallStackSaved[MAX_CALL_STACK_SAVE_SIZE];
int g_CallStackSavedSize = 0;


static void flush_file(int fd, const char *buf, size_t len) 
{
    while (len > 0)
	{
        ssize_t r = write(fd, buf, len);
        buf += r;
        len -= r;
    }
}

static void flush_callstack() 
{
    LLOG("flush_callstack");
    flush_file(gfd, (const char*)gCallStackSaved, sizeof(CallStack) * g_CallStackSavedSize);
    g_CallStackSavedSize = 0;
}

static void save_callstack(CallStack *pcs)
{
    LLOG("save_callstack");
    if (g_CallStackSavedSize >= MAX_CALL_STACK_SAVE_SIZE)
	{
        flush_callstack();
    }
    gCallStackSaved[g_CallStackSavedSize] = *pcs;
    g_CallStackSavedSize++;
}

static void flush() 
{
    if (g_ProfileData.total <= 0) 
	{
        return;
    }

    LLOG("flush...");

    int total = 0;
    for (int b = 0; b < MAX_BUCKET_SIZE; b++) 
	{
        Bucket *bucket = &g_ProfileData.bucket[b];
        for (int a = 0; a < MAX_CALL_STACK_SIZE; a++)
		{
            if (bucket->cs[a].count > 0) 
			{
                save_callstack(&bucket->cs[a]);
                bucket->cs[a].depth = 0;
                bucket->cs[a].count = 0;
                total++;
            }
        }
    }

    flush_callstack();

    for (auto iter = g_String2Id.begin(); iter != g_String2Id.end(); iter++)
	{
        const std::string &str = iter->first;
        int id = iter->second;

        int len = str.length();
        len = len > MAX_FUNC_NAME_SIZE ? MAX_FUNC_NAME_SIZE : len;
        flush_file(gfd, str.c_str(), len);
        flush_file(gfd, (const char *) &len, sizeof(len));

        flush_file(gfd, (const char *) &id, sizeof(id));
    }

    int len = g_String2Id.size();
    flush_file(gfd, (const char *) &len, sizeof(len));

    LLOG("flush ok %d %d", total, g_ProfileData.total);

    g_ProfileData.total = 0;

    if (gfd != 0)
	{
        close(gfd);
        gfd = 0;
    }

    printf("pLua flush ok\n");
}

static int lrealstop() 
{

    grunning = 0;

    struct itimerval timer;
    timer.it_interval.tv_sec = 0;
    timer.it_interval.tv_usec = 0;
    timer.it_value = timer.it_interval;
    int ret = setitimer(ITIMER_REAL, &timer, NULL);
    if (ret != 0) {
        LERR("setitimer fail %d", ret);
        return ret;
    }

    flush();
    return 0;
}

static void SignalHandlerHook(lua_State* L, lua_Debug* par) 
{

    LLOG("Hook...");

    lua_sethook(gL, 0, 0, 0);

    if (g_samplecount != 0 && g_samplecount <= g_ProfileData.total)
	{
        LLOG("lrealstop...");
        lrealstop();
        return;
    }

    g_ProfileData.total++;

    lua_Debug ar;

    int last = lastlevel(L); // 栈的起始index
    int i = 0;

    CallStack cs;
    cs.depth = 0;

    while (lua_getstack(L, last, &ar) && i < MAX_STACK_SIZE) // 从根到当前调用堆栈
	{
        lua_getinfo(L, "Slnt", &ar);
        pushfuncname(L, &ar);
        const char* funcname = lua_tostring(L, -1);
        lua_pop(L, 1);

        i++;
        last--; // 从栈底向上遍历

        int id = 0;
        auto iter = g_String2Id.find(funcname);
        if (iter == g_String2Id.end()) 
		{
            id = g_String2Id.size();
            g_String2Id[funcname] = id;
            g_Id2String[id] = funcname;
        }
		else 
		{
            id = iter->second;
        }
		
		if (id < VALID_MIN_ID)
		{
			continue;
		}

        LLOG("%s %d %d", funcname, id, last);

        cs.stack[cs.depth] = id;
        cs.depth++;
    }

    int hash = 0;
    for (int i = 0; i < cs.depth; i++)
	{
        int id = cs.stack[i];
        hash = (hash << 8) | (hash >> (8 * (sizeof(hash) - 1)));
        hash += (id * 31) + (id * 7) + (id * 3);
    }

    LLOG("hash %d", hash);

    bool done = false;
    Bucket* bucket = &g_ProfileData.bucket[(uint32_t) hash % MAX_BUCKET_SIZE];
    for (int a = 0; a < MAX_CALL_STACK_SIZE; a++)
	{
        CallStack* pcs = &bucket->cs[a];
        if (pcs->depth == 0 && pcs->count == 0) // 如果当前 bucket 未被使用
		{
            pcs->depth = cs.depth;
            pcs->count = 1;
            memcpy(pcs->stack, cs.stack, sizeof(int) * cs.depth);
            done = true;

            LLOG("hash %d add first %d %d", hash, pcs->count, pcs->depth);
            break;
        } 
		else if (pcs->depth == cs.depth) 
		{
            if (memcmp(pcs->stack, cs.stack, sizeof(int) * cs.depth) != 0) // 逐字节比较 == 0， 表示 str1 == str2
			{
                break;
            }
			else // hash 相同 && 调用深度相同 && stacks ids 相同 -> 确定是同一栈帧调用
			{
                pcs->count++; // 本stack层级调用的次数
                done = true;

                LLOG("hash %d add %d %d", hash, pcs->count, pcs->depth);
                break;
            }
        }
    }

    if (!done) 
	{
        CallStack* pcs = &bucket->cs[0];
        for (int a = 1; a < MAX_CALL_STACK_SIZE; a++)
		{
            if (bucket->cs[a].count < pcs->count)
			{
                pcs = &bucket->cs[a];
            }
        }

        if (pcs->count > 0) // if bucket is full ?
		{
            save_callstack(pcs);
        }

        // Use the newly evicted entry
        pcs->depth = cs.depth;
        pcs->count = 1;
        memcpy(pcs->stack, cs.stack, sizeof(int) * cs.depth);

        LLOG("hash %d add new %d %d", hash, pcs->count, pcs->depth);
    }

}

static void SignalHandler(int sig, siginfo_t* sinfo, void* ucontext)
{
	// hack lua5.3.4 linux-x64 为了判断是否不在lua中 L-nCcalls == 0
	//unsigned short nCcalls = *(unsigned short *)((char*)gL+198); // lua_State->nCcalls : number of nested C calls
	//if (nCcalls == 0)
	//{
	//	return;
	//}
	void* cframe = (void*)((char*)gL+48); // lua_State -> cframe
	if (cframe == NULL)
	{
		return;
	}
    lua_sethook(gL, SignalHandlerHook, LUA_MASKCOUNT, 1);
}

static int lrealstart(lua_State* L, int second, const char* file)
{
    if (grunning) 
	{
        LERR("start again, failed");
        return -1;
    }
    grunning = 1;
	
	g_String2Id["?"] = 0;
	g_Id2String[0] = "?";
	g_String2Id["function 'xpcall'"] = 1;
	g_Id2String[1] = "function 'xpcall'";
	g_String2Id["function 'pcall'"] = 2;
	g_Id2String[2] = "function 'pcall'";

    const int iter = 100;

    g_samplecount = second * 1000 / iter;
    g_filename = file;
    gL = L;

    LLOG("lstart %u %s", g_samplecount, file);

    struct sigaction sa;
    sa.sa_sigaction = SignalHandler;
    sa.sa_flags = SA_RESTART | SA_SIGINFO; // SA_RESTART 用于重新启动被信号中断的系统调用
    sigemptyset(&sa.sa_mask);

    if (sigaction(SIGALRM, &sa, NULL) == -1) 
	{
        LERR("sigaction(SIGALRM) failed");
        return -1;
    }

    struct itimerval timer;
    timer.it_interval.tv_sec = 0;
    timer.it_interval.tv_usec = 1 * 1000; // 100 ms 触发一次
    timer.it_value = timer.it_interval;
    int ret = setitimer(ITIMER_REAL, &timer, NULL);
    if (ret != 0) 
	{
        LERR("setitimer fail %d", ret);
        return -1;
    }

    memset(&g_ProfileData, 0, sizeof(g_ProfileData));
    memset(&gCallStackSaved, 0, sizeof(gCallStackSaved));
    memset(&g_CallStackSavedSize, 0, sizeof(g_CallStackSavedSize));

    int fd = open(file, O_CREAT | O_WRONLY | O_TRUNC, 0666);
    if (fd < 0) 
	{
        LERR("open file fail %s", file);
        return -1;
    }

    gfd = fd;

    return 0;
}

static int lstart(lua_State* L) 
{
    int second = (int) lua_tointeger(L, 1);
    const char *file = lua_tostring(L, 2);

    int ret = lrealstart(L, second, file);
    lua_pushinteger(L, ret);
    return 1;
}

static int lstop(lua_State* L)
{
    LLOG("lstop %s", g_filename.c_str());
    int ret = lrealstop();

    lua_pushinteger(L, ret);
    return 1;
}

static void load_file(int fd, char* buf, size_t len)
{
    while (len > 0)
	{
        ssize_t r = read(fd, buf, len);
        buf += r;
        len -= r;
    }
}

std::vector <CallStack> g_LoadCallStack;

static int load(const char* src_file)
{
    int fd = open(src_file, O_RDONLY, 0666);
    if (fd < 0)
	{
        LERR("open src_file fail %s", src_file);
        return -1;
    }

    int cnt = lseek(fd, 0, SEEK_END);

    int i = 0;

    int name_map_len = 0;
    i += sizeof(name_map_len);
    lseek(fd, -i, SEEK_END);
    load_file(fd, (char *) &name_map_len, sizeof(name_map_len));

    LLOG("name_map_len %d", name_map_len);

    int name_num = 0;
    while (i < cnt && name_num < name_map_len) 
	{
        int id = 0;
        i += sizeof(id);
        lseek(fd, -i, SEEK_END);
        load_file(fd, (char*)&id, sizeof(id)); // 读取符号id

        int name_len = 0;
        i += sizeof(name_len);
        lseek(fd, -i, SEEK_END);
        load_file(fd, (char *) &name_len, sizeof(name_len)); // 读取符号长度

        if (name_len > MAX_FUNC_NAME_SIZE)
		{
            LERR("open name_len fail %s %d", src_file, name_len);
            close(fd);
            return -1;
        }

        char str[MAX_FUNC_NAME_SIZE + 1];
        str[name_len] = 0;

        i += name_len;
        lseek(fd, -i, SEEK_END);
        load_file(fd, str, name_len); // 读取符号

        g_String2Id[str] = id;
        g_Id2String[id] = str;

        LLOG("name %d %s", id, str);
        name_num++;
    }

    g_LoadCallStack.clear();

    while (i < cnt) 
	{
        CallStack cs;

        i += sizeof(cs);
        lseek(fd, -i, SEEK_END);
        load_file(fd, (char*) &cs, sizeof(cs)); // 读取 call stack frame

        g_LoadCallStack.push_back(cs);

        LLOG("CallStack %d %d %s", cs.depth, cs.count, g_Id2String[cs.stack[cs.depth - 1]].c_str());
    }

    LLOG("load ok %d %d", g_String2Id.size(), g_LoadCallStack.size());

    close(fd);
    return 0;
}

static int output_text(const char* dst_file) 
{
    int fd = open(dst_file, O_CREAT | O_WRONLY | O_TRUNC, 0666);
    if (fd < 0) 
	{
        LERR("open dst_file fail %s", dst_file);
        return -1;
    }

    int total = 0;

    std::unordered_map<int, int> func_map;
    for (auto iter = g_LoadCallStack.begin(); iter != g_LoadCallStack.end(); iter++) 
	{
        const CallStack &cs = *iter;
        func_map[cs.stack[cs.depth - 1]] += cs.count;
        total += cs.count;
    }

    std::vector <std::pair<int, int>> func_arr;
    for (auto iter = func_map.begin(); iter != func_map.end(); iter++) 
	{
        func_arr.push_back(std::make_pair(iter->first, iter->second));
    }

    std::sort(func_arr.begin(), func_arr.end(), 
		[](const std::pair<int, int> &l, const std::pair<int, int> &r) {
			return r.second < l.second;
		}
    );

    std::stringstream ss;
    for (auto iter = func_arr.begin(); iter != func_arr.end(); iter++) 
	{
        ss << iter->second * 100 / total << "%\t" << g_Id2String[iter->first] << "\n";
    }

    LLOG("%s", ss.str().c_str())

    flush_file(fd, ss.str().c_str(), ss.str().length());

    close(fd);

    return 0;
}

static int ltext(lua_State* L)
{
    const char* src_file = lua_tostring(L, 1);
    const char* dst_file = lua_tostring(L, 2);

    int ret = load(src_file);
    if (ret != 0) 
	{
        LERR("load fail %d %s %s", ret, src_file, dst_file);
        lua_pushinteger(L, ret);
        return 1;
    }

    ret = output_text(dst_file);
    if (ret != 0) 
	{
        LERR("output_text fail %d %s %s", ret, src_file, dst_file);
        lua_pushinteger(L, ret);
        return 1;
    }

    lua_pushinteger(L, ret);
    return 1;
}

static int output_dot(const char* dst_file)
{
    int fd = open(dst_file, O_CREAT | O_WRONLY | O_TRUNC, 0666); // 新文件 && 置空
    if (fd < 0)
	{
        LERR("open dst_file fail %s", dst_file);
        return -1;
    }

    int total_self = 0;
    std::unordered_map<int, int> func_map_self; // cur_call symbol_id <--> count 
    for (auto iter = g_LoadCallStack.begin(); iter != g_LoadCallStack.end(); iter++)
	{
        const CallStack &cs = *iter;
        func_map_self[cs.stack[cs.depth - 1]] += cs.count;
        total_self += cs.count;
    }

    int total = 0; // 总栈帧数
    std::unordered_map<int, int> func_map; // every stack frame id <--> count
    for (auto iter = g_LoadCallStack.begin(); iter != g_LoadCallStack.end(); iter++) 
	{
        const CallStack &cs = *iter;
        for (int i = 0; i < cs.depth; i++)
		{
            func_map[cs.stack[i]] += cs.count;
        }
        total += cs.count;
    }

    std::vector <std::pair<int, int>> func_arr; // stack frame count sort (stack frame id <--> count)
    for (auto iter = func_map.begin(); iter != func_map.end(); iter++) 
	{
        func_arr.push_back(std::make_pair(iter->first, iter->second));
    }

    std::sort(func_arr.begin(), func_arr.end(), 
		[](const std::pair<int, int> &l, const std::pair<int, int> &r) {
			return r.second < l.second;
        }
    );

    struct pair_hash 
	{
        std::size_t operator()(const std::pair<int, int>& p) const
		{
            return ((size_t) p.first << 32) + p.second;
        }
    };

    std::set<int> has_son_set;
    std::unordered_set <std::pair<int, int>, pair_hash> func_call_set;
    for (auto iter = g_LoadCallStack.begin(); iter != g_LoadCallStack.end(); iter++) 
	{
        const CallStack &cs = *iter;
        for (int i = 0; i < cs.depth - 1; i++) 
		{
            func_call_set.insert(std::make_pair(cs.stack[i], cs.stack[i + 1]));
            has_son_set.insert(cs.stack[i]);
        }
    }

    std::stringstream ss;
    ss << "digraph G {\n";

    for (auto iter = func_arr.begin(); iter != func_arr.end(); iter++)
	{
        ss << "\tnode" << iter->first // symbol id
           << " [label=\"" << g_Id2String[iter->first] << "\\r" // symbol name
           << func_map_self[iter->first] << " (" << func_map_self[iter->first] * 100 / total_self << "%)" << "\\r"; // 

        if (has_son_set.find(iter->first) != has_son_set.end())
		{
            ss << iter->second << " (" << iter->second * 100 / total << "%)" << "\\r";
        }

        int fontsize = func_map_self[iter->first] * 100 / total_self; // 占比被收集到的帧越大字体越大
        if (fontsize < 10)
		{
            fontsize = 10;
        }

        ss << "\";"
           << "fontsize=" << fontsize
           << ";shape=box;"
           << "];\n";
    }

    for (auto iter = func_call_set.begin(); iter != func_call_set.end(); iter++)
	{
        const std::pair<int, int>& cp = *iter;
        float linewidth = func_map[cp.second] * 3.f / total;
        if (linewidth < 0.5f) 
		{
            linewidth = 0.5f;
        }
        ss << "\tnode" << cp.first << "->" << "node" << cp.second
           << " [style=\"setlinewidth(" << linewidth << ")\""
           << " label=" << func_map[cp.second]
           << "];\n";
    }

    ss << "}\n";

    LLOG("%s", ss.str().c_str())

    flush_file(fd, ss.str().c_str(), ss.str().length());

    close(fd);

    return 0;
}

static int ldot(lua_State* L) 
{
    const char* src_file = lua_tostring(L, 1);
    const char* dst_file = lua_tostring(L, 2);

    int ret = load(src_file);
    if (ret != 0)
	{
        LERR("load fail %d %s %s", ret, src_file, dst_file);
        lua_pushinteger(L, ret);
        return 1;
    }

    ret = output_dot(dst_file);
    if (ret != 0)
	{
        LERR("output_dot fail %d %s %s", ret, src_file, dst_file);
        lua_pushinteger(L, ret);
        return 1;
    }

    lua_pushinteger(L, ret);
    return 1;
}

static int lsvg(lua_State *L)
{
    const char *src_file = lua_tostring(L, 1);
    const char *dst_file = lua_tostring(L, 2);

    int ret = load(src_file);
    if (ret != 0) 
	{
        LERR("load fail %d %s %s", ret, src_file, dst_file);
        lua_pushinteger(L, ret);
        return 1;
    }

    std::string tmpdot = dst_file;
    tmpdot += ".dot";
    ret = output_dot(tmpdot.c_str());
    if (ret != 0) 
	{
        LERR("output_dot fail %d %s %s", ret, src_file, tmpdot.c_str());
        lua_pushinteger(L, ret);
        return 1;
    }

    GVC_t* gvc;
    Agraph_t* g;
    FILE* fp;
    gvc = gvContext();
    fp = fopen(tmpdot.c_str(), "r");
    g = agread(fp, 0);
    gvLayout(gvc, g, "dot");
    gvRender(gvc, g, "svg", fopen(dst_file, "w"));
    gvFreeLayout(gvc, g);
    agclose(g);
    gvFreeContext(gvc);

    lua_pushinteger(L, ret);
    return 1;

}

extern "C" int luaopen_libplua(lua_State *L) 
{
#if LUA_VERSION_NUM > 502
	luaL_checkversion(L);
#else
    luaL_Reg l[] = {
            {"start", lstart},
            {"stop",  lstop},
            {"text",  ltext},
            {"dot",   ldot},
            {"svg",   lsvg},
            {NULL,    NULL},
    };
#if LUA_VERSION_NUM < 502
	luaL_register(L, "plua", l);
#else
	luaL_newlib(L, l);
#endif
    return 1;
}
