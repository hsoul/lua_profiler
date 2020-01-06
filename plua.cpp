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
#include <iomanip>
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

// static const int VALID_MIN_ID = 3; // 最小符号ID
static const int MAX_STACK_SIZE = 64; // 堆栈的最大深度
static const int MAX_CALL_STACK_SIZE = 4; // bucket 存放最大的堆栈数量
static const int MAX_BUCKET_SIZE = 1 << 10;
static const int MAX_CALL_STACK_SAVE_SIZE = 1 << 18;
static const int MAX_FUNC_NAME_SIZE = 127; // 最长的函数（符号）名字

struct StackFrame
{
public:
	StackFrame()
	{
		line_defined_ = 0;
		current_line_ = 0;
	}
	bool operator== (const StackFrame& p) const
	{
		return func_name_ == p.func_name_ &&
			source_ == p.source_ &&
			line_defined_ == p.line_defined_;
	}
public:
	std::string func_name_;
	std::string source_;
	int line_defined_;
	int current_line_;
};

struct FrameHash
{
	std::size_t operator()(const StackFrame& key) const
	{
		return std::hash<decltype(key.func_name_)>()(key.func_name_) + std::hash<decltype(key.source_)>()(key.source_) + std::hash<int>()(key.line_defined_);
	}
};

struct CallStacks
{
	int count_; // count = 0 表示未被使用
	int depth_;
	int stacks_[MAX_STACK_SIZE];
};

struct Bucket
{
	CallStacks call_stacks_[MAX_CALL_STACK_SIZE];
};

struct ProfileData
{
	Bucket buckets_[MAX_BUCKET_SIZE];
	int total_num_;
};

int g_open_debug = 0; // 是否输出日志
int g_sample_count; // 采样数量
std::string g_file_name; // 收集的数据文件
lua_State* g_L;
int g_running = 0; // 当前是否正在运行
int g_fd; // 收集的数据文件的 file handle
ProfileData g_profile_data; // 内存中收集的堆栈数据(哈希表存储)
CallStacks g_call_stack_saved[MAX_CALL_STACK_SAVE_SIZE]; // 如果g_profile_data 中某个 bucket 满了， 先将当前堆栈数据存放于 g_call_stack_saved 缓存，如果缓存达到一定数量，写入数据文件 
int g_call_stack_saved_size = 0; // 当前缓存数量
std::vector <CallStacks> g_load_call_stack; // 生成图时在数据文件中加载的所有堆栈
std::unordered_map<StackFrame, int, FrameHash> g_stack_frame_ids; // 收集时使用
std::unordered_map<int, StackFrame> g_id_stack_frames; // 输出图表时使用

#define LLOG(...) if (g_open_debug) {llog("[DEBUG] ", __FILE__, __FUNCTION__, __LINE__, __VA_ARGS__);}
#define LERR(...) if (g_open_debug) {llog("[ERROR] ", __FILE__, __FUNCTION__, __LINE__, __VA_ARGS__);}

void llog(const char* header, const char* file, const char* func, int pos, const char* fmt, ...) 
{
    FILE* pLog = NULL;
    time_t clock1;
    struct tm* tptr;
    va_list ap;

    pLog = fopen("plua.log", "a+");
    if (pLog == NULL)
	{
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

static int findfield(lua_State* L, int obj_idx, int level) // search for 'obj_idx' in table at index -1. return 1 + string at top if find a good name. obj_idx 正数， level 遍历层级， if find object push object name onto stack
{
    if (level == 0 || !lua_istable(L, -1))
        return 0;  /* not found */
    lua_pushnil(L);  /* start 'next' loop */
    while (lua_next(L, -2)) /* for each pair in table */ // Pops a key from the stack, and pushes a key-value pair from the table at the given index (the "next" pair after the given key). If there are no more elements in the table, then lua_next returns 0 (and pushes nothing).
	{  
        if (lua_type(L, -2) == LUA_TSTRING) /* ignore non-string keys */
		{  
            if (lua_rawequal(L, obj_idx, -1)) /* found object? */
			{  
                lua_pop(L, 1);  /* remove value (but keep name) */
                return 1;
            }
			else if (findfield(L, obj_idx, level - 1)) /* try recursively */
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

static int pushglobalfuncname(lua_State* L, lua_Debug* ar) // Search for a name for a function in all loaded modules
{
    int top = lua_gettop(L);
    lua_getinfo(L, "f", ar);  /* push function */
    lua_getfield(L, LUA_REGISTRYINDEX, "_LOADED");
    if (findfield(L, top + 1, 2)) 
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
		// printf("######### global func name\n");
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

static void flush_file(int fd, const char* buf, size_t len) 
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
    flush_file(g_fd, (const char*)g_call_stack_saved, sizeof(CallStacks) * g_call_stack_saved_size);
    g_call_stack_saved_size = 0;
}

static void save_callstack(CallStacks* pcs)
{
    LLOG("save_callstack");
    if (g_call_stack_saved_size >= MAX_CALL_STACK_SAVE_SIZE)
	{
        flush_callstack();
    }
    g_call_stack_saved[g_call_stack_saved_size] = *pcs;
    g_call_stack_saved_size++;
}

static void flush() 
{
    if (g_profile_data.total_num_ <= 0) 
	{
        return;
    }

    LLOG("flush...");

    int total = 0;
    for (int b = 0; b < MAX_BUCKET_SIZE; b++) 
	{
        Bucket* bucket = &g_profile_data.buckets_[b];
        for (int a = 0; a < MAX_CALL_STACK_SIZE; a++)
		{
            if (bucket->call_stacks_[a].count_ > 0) 
			{
                save_callstack(&bucket->call_stacks_[a]);
                bucket->call_stacks_[a].depth_ = 0;
                bucket->call_stacks_[a].count_ = 0;
                total++;
            }
        }
    }

    flush_callstack();

    LLOG("flush ok %d %d", total, g_profile_data.total_num_);

    g_profile_data.total_num_ = 0;

    if (g_fd != 0)
	{
        close(g_fd);
        g_fd = 0;
    }

    printf("pLua flush ok\n");
}

static int lrealstop() 
{

    g_running = 0;

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

    lua_sethook(g_L, 0, 0, 0);

    if (g_sample_count != 0 && g_sample_count <= g_profile_data.total_num_)
	{
        LLOG("lrealstop...");
        lrealstop();
        return;
    }

    g_profile_data.total_num_++;

    lua_Debug ar;

    int last = lastlevel(L); // 栈的起始index
    int i = 0;

    CallStacks cs;
	cs.depth_ = 0;
	StackFrame stack_frame;

    while (lua_getstack(L, last, &ar) && i < MAX_STACK_SIZE) // 从根到当前调用堆栈
	{
        lua_getinfo(L, "Slnt", &ar);
        pushfuncname(L, &ar);
        const char* funcname = lua_tostring(L, -1);
        lua_pop(L, 1);

		stack_frame.func_name_ = funcname;
		stack_frame.source_ = ar.source;
		stack_frame.line_defined_ = ar.linedefined;
		stack_frame.current_line_ = ar.currentline;

		int id = 0;
		auto iter = g_stack_frame_ids.find(stack_frame);
		if (iter != g_stack_frame_ids.end())
		{
			id = iter->second;
		}
		else
		{
			id = g_stack_frame_ids.size();
			g_stack_frame_ids[stack_frame] = g_stack_frame_ids.size();
			g_id_stack_frames[id] = stack_frame;
		}

        i++;
        last--; // 从栈底向上遍历

        LLOG("%s %d %d", funcname, id, last);

		cs.stacks_[cs.depth_] = id;
		cs.depth_++;
    }

    int hash = 0;
    for (int i = 0; i < cs.depth_; i++)
	{
        int id = cs.stacks_[i];
        hash = (hash << 8) | (hash >> (8 * (sizeof(hash) - 1)));
        hash += (id * 31) + (id * 7) + (id * 3);
    }

    LLOG("hash %d", hash);

    bool done = false;
    Bucket* bucket = &g_profile_data.buckets_[(uint32_t) hash % MAX_BUCKET_SIZE];
    for (int a = 0; a < MAX_CALL_STACK_SIZE; a++)
	{
        CallStacks* pcs = &bucket->call_stacks_[a];
        if (pcs->depth_ == 0 && pcs->count_ == 0) // 如果当前 bucket 未被使用
		{
            pcs->depth_ = cs.depth_;
            pcs->count_ = 1;
            memcpy(pcs->stacks_, cs.stacks_, sizeof(int) * cs.depth_);
            done = true;

            LLOG("hash %d add first %d %d", hash, pcs->count_, pcs->depth_);
            break;
        } 
		else if (pcs->depth_ == cs.depth_) 
		{
            if (memcmp(pcs->stacks_, cs.stacks_, sizeof(int) * cs.depth_) != 0) // 逐字节比较 == 0， 表示 str1 == str2
			{
                break;
            }
			else // hash 相同 && 调用深度相同 && stacks ids 相同 -> 确定是同一栈帧调用
			{
                pcs->count_++; // 本stack层级调用的次数
                done = true;

                LLOG("hash %d add %d %d", hash, pcs->count_, pcs->depth_);
                break;
            }
        }
    }

    if (!done) 
	{
        CallStacks* pcs = &bucket->call_stacks_[0];
        for (int a = 1; a < MAX_CALL_STACK_SIZE; a++)
		{
            if (bucket->call_stacks_[a].count_ < pcs->count_)
			{
                pcs = &bucket->call_stacks_[a];
            }
        }

        if (pcs->count_ > 0) // if bucket is full
		{
            save_callstack(pcs);
        }

        // Use the newly evicted entry
        pcs->depth_ = cs.depth_;
        pcs->count_ = 1;
        memcpy(pcs->stacks_, cs.stacks_, sizeof(int) * cs.depth_);

        LLOG("hash %d add new %d %d", hash, pcs->count_, pcs->depth_);
    }

}

static void SignalHandler(int sig, siginfo_t* sinfo, void* ucontext)
{
	// hack lua5.3.4 linux-x64 为了判断是否不在lua中 L-nCcalls == 0
	//unsigned short nCcalls = *(unsigned short *)((char*)g_L+198); // lua_State->nCcalls : number of nested C calls
	//if (nCcalls == 0)
	//{
	//	return;
	//}
	void* cframe = (void*)((char*)g_L+48); // lua_State -> cframe
	if (cframe == NULL)
	{
		return;
	}
    lua_sethook(g_L, SignalHandlerHook, LUA_MASKCOUNT, 1);
}

static int lrealstart(lua_State* L, int second, const char* file)
{
    if (g_running) 
	{
        LERR("start again, failed");
        return -1;
    }
    g_running = 1;
	
    const int iter = 100;

    g_sample_count = second * 1000 / iter;
    g_file_name = file;
    g_L = L;

    LLOG("lstart %u %s", g_sample_count, file);

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

    memset(&g_profile_data, 0, sizeof(g_profile_data));
    memset(&g_call_stack_saved, 0, sizeof(g_call_stack_saved));
    memset(&g_call_stack_saved_size, 0, sizeof(g_call_stack_saved_size));

    int fd = open(file, O_CREAT | O_WRONLY | O_TRUNC, 0666);
    if (fd < 0) 
	{
        LERR("open file fail %s", file);
        return -1;
    }

    g_fd = fd;

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
    LLOG("lstop %s", g_file_name.c_str());
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

	g_load_call_stack.clear();

    while (i < cnt) 
	{
        CallStacks cs;

        i += sizeof(cs);
        lseek(fd, -i, SEEK_END);
        load_file(fd, (char*) &cs, sizeof(cs)); // 读取 call stack frame

        g_load_call_stack.push_back(cs);

		auto iter = g_id_stack_frames.find(cs.stacks_[cs.depth_ - 1]);
		if (iter != g_id_stack_frames.end())
		{
			StackFrame& stack_frame = iter->second;
			LLOG("CallStacks %d %d %s %s:%s", cs.depth_, cs.count_, stack_frame.func_name_, stack_frame.source_, stack_frame.line_defined_);
		}
		else
		{
			LLOG("load() can not find id [%d] frame", cs.stacks_[cs.depth_ - 1]);
		}
    }

    LLOG("load ok %d", g_load_call_stack.size());

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
    for (auto iter = g_load_call_stack.begin(); iter != g_load_call_stack.end(); iter++) 
	{
        const CallStacks &cs = *iter;
		for (int i = 0; i < cs.depth_; ++i)
		{
			func_map[cs.stacks_[i]] += cs.count_;
		}
        total += cs.count_;
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
	ss << "collect total num is " << total << "\n";
	ss << std::setw(64) << std::setiosflags(std::ios::left) << "FILE_NAME";
	ss << std::setw(48) << std::setiosflags(std::ios::left) << "FUNCTION_NAME";  
	ss << std::setw(24) << std::setiosflags(std::ios::left) << "LINE_DEFINED";
	ss << std::setw(24) << std::setiosflags(std::ios::left) << "HIT_COUNT";
	ss << std::setw(24) << std::setiosflags(std::ios::left)<< "PERCENT";
	ss << "\n";
    for (auto iter = func_arr.begin(); iter != func_arr.end(); iter++) 
	{
		StackFrame sf = g_id_stack_frames[iter->first];
		ss << std::setw(64) << std::setiosflags(std::ios::left) << sf.source_;
		ss << std::setw(48) << std::setiosflags(std::ios::left) << sf.func_name_;	
		ss << std::setw(24) << std::setiosflags(std::ios::left) << sf.line_defined_;
		ss << std::setw(24) << std::setiosflags(std::ios::left) << iter->second;
		ss << std::setw(8) << std::setiosflags(std::ios::left)<< (double)(iter->second) * 100 / total << "%" << "\n";
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
    for (auto iter = g_load_call_stack.begin(); iter != g_load_call_stack.end(); iter++)
	{
        const CallStacks &cs = *iter;
        func_map_self[cs.stacks_[cs.depth_ - 1]] += cs.count_;
        total_self += cs.count_;
    }

    int total = 0; // 总栈帧数
    std::unordered_map<int, int> func_map; // every stack frame id <--> count_
    for (auto iter = g_load_call_stack.begin(); iter != g_load_call_stack.end(); iter++) 
	{
        const CallStacks &cs = *iter;
        for (int i = 0; i < cs.depth_; i++)
		{
            func_map[cs.stacks_[i]] += cs.count_;
        }
        total += cs.count_;
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
    for (auto iter = g_load_call_stack.begin(); iter != g_load_call_stack.end(); iter++) 
	{
        const CallStacks &cs = *iter;
        for (int i = 0; i < cs.depth_ - 1; i++) 
		{
            func_call_set.insert(std::make_pair(cs.stacks_[i], cs.stacks_[i + 1]));
            has_son_set.insert(cs.stacks_[i]);
        }
    }

    std::stringstream ss;
    ss << "digraph G {\n";

    for (auto iter = func_arr.begin(); iter != func_arr.end(); iter++)
	{
		StackFrame stack_frame = g_id_stack_frames[iter->first];
        ss << "\tnode" << iter->first // symbol id
           << " [label=\"" << stack_frame.func_name_ << "\\r" // symbol name
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

static int lsvg(lua_State* L)
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

extern "C" int luaopen_libplua(lua_State* L) 
{
#if LUA_VERSION_NUM > 502
	luaL_checkversion(L);
#endif
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
