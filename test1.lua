
function test()

	for i = 1, 1000 do
		test1(i)
	end

end

function test1(n)

	for i = 1, 1000 do
		local j = i*n
		local f = "test2"..((i % 5) + 1)
		_G[f](j)
	end

end

function test21(n)

	for i = 1, 1000 do
		local j = i*n
	end

end

function test22(n)

	for i = 1, 1000 do
		local j = i*n
	end

end

function test23(n)

	for i = 1, 1000 do
		local j = i*n
	end

end

function test24(n)

	for i = 1, 1000 do
		local j = i*n
	end

end

function test25(n)

	for i = 1, 1000 do
		local j = i*n
	end

end

if jit then
	jit.off()
	jit.flush()
end

local p = require "libplua"

p.start(0, "call.pro")

test()

p.stop()

p.text("call.pro", "call.txt")
p.dot("call.pro", "call.dot")
p.svg("call.pro", "call.svg")