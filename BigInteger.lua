--[[
	// BigInteger.js
	// Available under Public Domain
	// https://github.com/Yaffle/BigInteger/

	// For implementation details, see "The Handbook of Applied Cryptography"
	// http://www.cacr.math.uwaterloo.ca/hac/about/chap14.pdf
]]

--[[
	-- BigInteger.lua
	-- Available under Public Domain
	-- https://github.com/romdotdog/BigInteger.lua
]]

--

local createArray = table.create
local byte = string.byte
local sub = string.sub
local floor = math.floor

--

local epsilon = 2 / (9007199254740991 + 1)
while 1 + epsilon / 2 ~= 1 do
	epsilon /= 2
end

local BASE = 2 / epsilon
local s = 134217728

while s * s < 2 / epsilon do
	s *= 2
end

local SPLIT = s + 1

local function fma(a, b, product)
	local at = SPLIT * a
	local ahi = at - (at - a)
	local alo = a - ahi
	local bt = SPLIT * b
	local bhi = bt - (bt - b)
	local blo = b - bhi
	return ((ahi * bhi + product) + ahi * blo + alo * bhi) + alo * blo
end

local function fastTrunc(x)
	local v = (x - BASE) + BASE
	return v > x and v - 1 or v
end

local function performMultiplication(carry, a, b)
	local product = a * b
	local err = fma(a, b, -product)

	local hi = (product / BASE) - BASE + BASE
	local lo = product - hi * BASE + err

	if lo >= 0 then
		lo -= BASE
		hi += 1
	end

	lo += carry
	if lo < 0 then
		lo += BASE
		hi -= 1
	end

	return lo, hi
end

local function performDivision(a, b, divisor)
	if a >= divisor then
		error()
	end

	local p = a * BASE
	local q = fastTrunc(p / divisor)

	local r = 0 - fma(q, divisor, -p)
	if r < 0 then
		q -= 1
		r += divisor
	end

	r += b - divisor
	if r < 0 then
		r += divisor
	else
		q += 1
	end

	local y = fastTrunc(r / divisor)
	r -= y * divisor
	q += y
	return q, r
end

local mt = {}
mt.__index = mt

local function createBigInteger(sign, magnitude, length)
	local t = createArray(3)
	t[1] = sign
	t[2] = magnitude
	t[3] = length

	setmetatable(t, mt)
	return t
end

local function fromNumber(n)
	if n >= BASE or 0 - n >= BASE then
		error("Cannot store number, it is too inaccurate. Please represent in string.")
	end

	local a = createArray(1, 0)
	a[1] = n < 0 and 0 - n or 0 + n
	return createBigInteger(n < 0 and 1 or 0, a, n == 0 and 0 or 1)
end

local function fromString(s: string)
	local length = #s
	if length == 0 then
		error("Blank string passed to `new`")
	end

	local sign = 0
	local signCharCode = byte(s, 1)
	local from = 0
	if signCharCode == 43 then -- +
		from = 1
	end
	if signCharCode == 45 then -- -
		from = 1
		sign = 1
	end
	local radix = 10
	if from == 0 and length >= 2 and byte(s, 1) == 48 then -- 0
		local cha = byte(s, 2)
		if cha == 98 then -- b
			from = 2
		elseif cha == 111 then -- o
			radix = 8
			from = 2
		elseif cha == 88 or cha == 120 then -- Xx
			radix = 16
			from = 2
		end
	end
	length -= from
	if length == 0 then
		error("Blank string passed to `new`")
	end

	local groupLength = 0
	local groupRadix = 1
	local limit = fastTrunc(BASE / radix)
	while groupRadix <= limit do
		groupLength += 1
		groupRadix *= radix
	end

	local size = floor((length - 1) / groupLength) + 1
	local magnitude = createArray(size, 0)
	local start = from + 1 + (length - 1 - (size - 1) * groupLength) - groupLength

	for j = 0, size - 1 do
		local groupStart = start + j * groupLength
		local c = tonumber(sub(s, (groupStart >= from and groupStart or from) + 1, groupStart + groupLength), radix)
		for l = 1, j do
			magnitude[l], c = performMultiplication(c, magnitude[l], groupRadix)
		end
		magnitude[j + 1] = c
	end

	while size > 0 and magnitude[size] == 0 do
		size -= 1
	end

	return createBigInteger(size == 0 and 0 or sign, magnitude, size)
end

function mt.new(x)
	if type(x) == "number" then
		return fromNumber(x)
	end
	if type(x) == "string" then
		return fromString(x)
	end
	error("Invalid type passed to `new`, expected number or string")
end

function mt.toNumber(a)
	local size = a[3]
	if size == 0 then
		return 0
	end

	local mag = a[2]
	if size == 1 then
		return a[1] == 1 and 0 - mag[1] or mag[1]
	end

	if BASE + 1 ~= BASE then
		error("BaseError")
	end

	local x = mag[size]
	local y = mag[size - 1]
	local i = size - 2
	while i > 0 and mag[i] == 0 do
		i -= 1
	end

	if i > 0 and y % 2 == 1 then
		y += 1
	end

	local z = (x * BASE + y) * BASE ^ (size - 2)
	return a[1] == 1 and 0 - z or z
end

-- Find some way to compare tables fast?
-- I removed the initial magnitude equality.
local function compareMagnitude(a, b)
	local al, bl = a[3], b[3]
	if al ~= bl then
		return al < bl and -1 or 1
	end

	local am, bm = a[2], b[2]
	for i = al, 1, -1 do
		local ai, bi = am[i], bm[i]
		if ai ~= bi then
			return ai < bi and -1 or 1
		end
	end

	return 0
end

local function compareTo(a, b)
	local as = a[1]
	local c = as == b[1] and compareMagnitude(a, b) or 1
	return as == 1 and 0 - c or c
end

function mt.__lt(a, b)
	return compareTo(a, b) < 0
end

function mt.__le(a, b)
	return compareTo(a, b) <= 0
end

function mt.__eq(a, b)
	return compareTo(a, b) == 0
end

local function addAndSubtract(a, b, isSubtraction)
	local z = compareMagnitude(a, b)
	local resultSign = z < 0 and (isSubtraction ~= 0 and 1 - b[1] or b[1]) or a[1]
	local min = z < 0 and a or b
	local max = z < 0 and b or a
	local nm, xm = min[2], max[2]

	if min[3] == 0 then
		return createBigInteger(resultSign, xm, max[3])
	end

	local subtract = 0
	local resultLength = max[3]
	if a[1] ~= (isSubtraction ~= 0 and 1 - b[1] or b[1]) then
		subtract = 1
		if min[3] == resultLength then
			while resultLength > 0 and nm[resultLength] == xm[resultLength] do
				resultLength -= 1
			end
		end
		if resultLength == 0 then -- a == -b
			return createBigInteger(0, {}, 0)
		end
	end

	-- result ~= 0
	local result = createArray(resultLength + (1 - subtract), 0)
	local c = 0

	for i = 1, min[3] do
		local aDigit = nm[i]
		c += xm[i] + (subtract ~= 0 and 0 - aDigit or aDigit - BASE)
		if c < 0 then
			result[i] = BASE + c
			c = 0 - subtract
		else
			result[i] = c
			c = 1 - subtract
		end
	end

	for i = min[3] + 1, resultLength do
		c += xm[i]
		if subtract == 0 then
			c += 0 - BASE
		end
		if c < 0 then
			result[i] = BASE + c
			c = 0 - subtract
		else
			result[i] = c
			c = 1 - subtract
		end
	end

	if subtract == 0 then
		result[resultLength + 1] = c
		if c ~= 0 then
			resultLength += 1
		end
	else
		while resultLength > 0 and result[resultLength] == 0 do
			resultLength -= 1
		end
	end

	return createBigInteger(resultSign, result, resultLength)
end

function mt.__add(a, b)
	return addAndSubtract(a, b, 0)
end

function mt.__sub(a, b)
	return addAndSubtract(a, b, 1)
end

function mt.__mul(a, b)
	local alength = a[3]
	local blength = b[3]
	local am = a[2]
	local bm = b[2]
	local asign = a[1]
	local bsign = b[1]
	if alength == 0 or blength == 0 then
		return createBigInteger(0, {}, 0)
	end
	if alength == 1 and am[1] == 1 then
		return createBigInteger(asign == 1 and 1 - bsign or bsign, bm, blength)
	end
	if blength == 1 and bm[1] == 1 then
		return createBigInteger(asign == 1 and 1 - bsign or bsign, am, alength)
	end
	local astart = 1
	while am[astart] == 0 do
		astart += 1
	end
	local resultSign = asign == 1 and 1 - bsign or bsign
	local resultLength = alength + blength
	local result = createArray(resultLength, 0)
	for i = 1, blength do
		local digit = bm[i]
		if digit ~= 0 then
			local c = 0
			for j = astart, alength do
				local ij = j + i - 1
				local carry = 1
				c += result[ij] - BASE
				if c < 0 then
					c += BASE
					carry = 0
				end
				local lo, hi = performMultiplication(c, am[j], digit)
				result[ij] = lo
				c = hi + carry
			end
			result[alength + i] = c
		end
	end
	if result[resultLength] == 0 then
		resultLength -= 1
	end
	return createBigInteger(resultSign, result, resultLength)
end

local function divideAndRemainder(a, b, isDivision)
	local alength = a[3]
	local blength = b[3]
	local am = a[2]
	local bm = b[2]
	local asign = a[1]
	local bsign = b[1]
	if blength == 0 then
		error("Attempt to divide by zero")
	end
	if alength == 0 then
		return createBigInteger(0, {}, 0)
	end
	local quotientSign = asign == 1 and 1 - bsign or bsign
	if blength == 1 and bm[1] == 1 then
		if isDivision ~= 0 then
			return createBigInteger(quotientSign, am, alength)
		end
		return createBigInteger(0, {}, 0)
	end

	local divisorOffset = alength + 1
	local divisorAndRemainder = createArray(divisorOffset + blength + 1, 0)
	local divisor = divisorAndRemainder
	local remainder = divisorAndRemainder
	for n = 1, alength do
		remainder[n] = am[n]
	end
	for m = 1, blength do
		divisor[divisorOffset + m] = bm[m]
	end

	local top = divisor[divisorOffset + blength]

	-- normalization
	local lambda = 1
	if blength > 1 then
		lambda = fastTrunc(BASE / (top + 1))
		if lambda > 1 then
			local carry = 0
			for l = 1, divisorOffset + blength do
				local lo, hi = performMultiplication(carry, divisorAndRemainder[l], lambda)
				divisorAndRemainder[l] = lo
				carry = hi
			end
			divisorAndRemainder[divisorOffset + blength + 1] = carry
			top = divisor[divisorOffset + blength]
		end

		if top < fastTrunc(BASE / 2) then
			error()
		end
	end

	local shift = alength - blength
	if shift < 0 then
		shift = 0
	end

	local quotient
	local quotientLength = 0

	local lastNonZero = 1
	while divisor[divisorOffset + lastNonZero] == 0 do
		lastNonZero += 1
	end

	for i = shift, 0, -1 do
		local t = blength + i
		local t1 = t + 1

		local q = BASE - 1
		if remainder[t1] ~= top then
			q = performDivision(remainder[t1], remainder[t], top)
		end

		local ax = 0
		local bx = 0

		local z = i + lastNonZero
		for j = z, t1 do
			local lo, hi = performMultiplication(bx, q, divisor[divisorOffset + j - i])
			bx = hi
			ax += remainder[j] - lo
			if ax < 0 then
				remainder[j] = BASE + ax
				ax = -1
			else
				remainder[j] = ax
				ax = 0
			end
		end

		while ax ~= 0 do
			q -= 1
			local c = 0
			for k = z, t1 do
				c += remainder[k] - BASE + divisor[divisorOffset + k - i]
				if c < 0 then
					remainder[k] = BASE + c
					c = 0
				else
					remainder[k] = c
					c = 1
				end
			end
			ax += c
		end

		if isDivision ~= 0 and q ~= 0 then
			if quotientLength == 0 then
				quotientLength = i + 1
				quotient = createArray(quotientLength, 0)
			end
			quotient[i + 1] = q
		end
	end

	if isDivision ~= 0 then
		if quotientLength == 0 then
			return createBigInteger(0, {}, 0)
		end
		return createBigInteger(quotientSign, quotient, quotientLength)
	end

	local remainderLength = alength + 1
	if lambda > 1 then
		local r = 0
		for p = remainderLength, 1, -1 do
			local q
			q, r = performDivision(r, remainder[p], lambda)
			remainder[p] = q
		end
		if r ~= 0 then
			error()
		end
	end

	while remainderLength > 0 and remainder[remainderLength] == 0 do
		remainderLength -= 1
	end

	if remainderLength == 0 then
		return createBigInteger(0, {}, 0)
	end

	local result = createArray(remainderLength, 0)
	for o = 1, remainderLength do
		result[o] = remainder[o]
	end

	return createBigInteger(asign, result, remainderLength)
end

function mt.__div(a, b)
	return divideAndRemainder(a, b, 1)
end

function mt.__mod(a, b)
	local fa = divideAndRemainder(a, b, 0)
	if a[1] + b[1] == 0 then -- a > 0 and b > 0
		return fa
	end
	return divideAndRemainder(
		fa + b,
		b, 0
	)
end

function mt.__unm(a)
	return createBigInteger(a[3] == 0 and a[1] or 1 - a[1], a[2], a[3])
end

local two = mt.new(2)

local log = math.log
function mt.__pow(a, b)
	local n = b:toNumber()
	if n < 0 then
		error()
	end

	if n > 9007199254740991 then
		local y = a:toNumber()
		if y == 0 or y == -1 or y == 1 then
			return y == -1 and (b % 2):toNumber() == 0 and -a or a
		end
		error()
	end

	if n == 0 then
		return mt.new(1)
	end

	local am = a[2]
	local af = am[1]
	if a[3] == 1 and (af == 2 or af == 16) then
		local log2 = log(2)
		local bits = floor(log(BASE) / log2 + 0.5)
		local abits = floor(log(af) / log2 + 0.5)
		local nn = abits * n
		local q = floor(nn / bits)
		local q1 = q + 1
		local r = nn - q * bits
		local array = createArray(q1, 0)
		array[q1] = 2 ^ r
		return createBigInteger((af == 0 or n % 2 == 0) and 0 or 1, array, q1)
	end

	local x = a
	while n % 2 == 0 do
		n = floor(n / 2)
		x *= x
	end

	local accumulator = x
	n -= 1
	if n >= 2 then
		while n >= 2 do
			local t = floor(n / 2)
			if t * 2 ~= n then
				accumulator *= x
			end
			n = t
			x *= x
		end
		accumulator *= x
	end
	return accumulator
end

local new = mt.new
local rep = string.rep
local format = string.format
local insert = table.insert
local concat = table.concat

local formatBases = {
	[8] = "o",
	[10] = "d",
	[16] = "x"
}

local digits = "0123456789abcdefghijklmnopqrstuvwxyz"
local abs = math.abs
local function basen(n, b)
	local fb = formatBases[b or 10]
	if fb then
		return format("%.0"..fb, n)
	end
	n = floor(abs(n))
	local t = {}
	repeat
		local d = (n % b) + 1
		n = floor(n / b)
		insert(t, 1, sub(digits, d, d))
	until n == 0
	return concat(t)
end

local function toString(this, radix)
	if radix == nil then radix = 10 end
	if radix ~= 10 and (radix < 2 or radix > 36 or radix ~= floor(radix)) then
		error("radix argument must be an integer between 2 and 36")
	end

	local thisl = this[3]
	if thisl > 8 then
		if this[1] == 1 then
			return "-" .. toString(-this, radix)
		end

		local e = floor(thisl * log(BASE) / log(radix) / 2 + 0.5 - 1)
		local split = new(radix) ^ new(e)
		local q = this / split
		local r = this - q * split
		local a = toString(r, radix)
		return toString(q, radix) .. rep("0", e - #a) .. a
	end

	local remainderLength = thisl
	if remainderLength == 0 then
		return "0"
	end

	local a = this
	local result = {a[1] == 1 and "-" or ""}

	if remainderLength == 1 then
		insert(result, basen(a[2][1], radix))
		return concat(result)
	end

	local groupLength = 0
	local groupRadix = 1
	local limit = fastTrunc(BASE / radix)
	while groupRadix <= limit do
		groupLength += 1
		groupRadix *= radix
	end

	if groupRadix * radix <= BASE then
		error()
	end

	local size = remainderLength + floor((remainderLength - 1) / groupLength) + 1
	local remainder = createArray(size, 0)

	local am = a[2]
	for n = 1, remainderLength do
		remainder[n] = am[n]
	end

	local k = size
	while remainderLength ~= 0 do
		local groupDigit = 0
		for i = remainderLength, 1, -1 do
			remainder[i], groupDigit = performDivision(groupDigit, remainder[i], groupRadix)
		end
		while remainderLength > 0 and remainder[remainderLength] == 0 do
			remainderLength -= 1
		end
		remainder[k] = groupDigit
		k -= 1
	end
	k += 1
	insert(result, basen(remainder[k], radix))

	for i = k + 1, size do
		local t = basen(remainder[i], radix)
		insert(result, rep("0", groupLength - #t))
		insert(result, t)
	end
	return concat(result)
end

mt.__tostring = toString
mt.toString = toString

return mt