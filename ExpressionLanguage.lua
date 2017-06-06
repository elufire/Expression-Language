#include <lua.hpp>

--[[ UTILITY FUNCTIONS

These functions are used for output and error messages.

--]]

-- Function "show_data" converts raw Lua data structures to strings to
-- assist in debugging and testing. This assumes the structure is
-- acyclic. 



local function show_data(d)
   if type(d) == "table" then
      local res = {}
      for k,v in pairs(d) do
        res[#res+1] = "[" .. show_data(k) .. "] = " .. show_data(v)
       end
      return "(" .. table.concat(res, ", ") .. ")"
   else
      return tostring(d)
   end
end

-- Function "treeConcat" takes a recursive list of lists in "array"
-- argument "t" and returns the corresponding parenthesized traversal
-- string.  A list is stored in the low positive integer indices of an
-- array-style Lua table. This assumes the structure is acyclic.

local function treeConcat(t)
   if type(t) ~= "table" then return tostring(t) end
   local res = {}
   for i = 1, #t do
      res[i] = treeConcat(t[i])
   end
   return "(" .. table.concat(res," ") .. ")"
end


--[[  ABSTRACT SYNTAX FOR EXPRESSIONS

This layer encapsulates the representation of Expressions behind
constructors and accessors.  Other part of the program should
only access the data structure through the public functions. This
design allows the representation to change with few effects on the
other parts of the interpreter.

This layer represents the abstract syntax for the Expression Language
using Lua array tables as indicated below. Field 1 is a type tag.

Expr ==
   {INT, number}             -- integer value
   {VAR, string}             -- variable name
   {NEG, Expr}               -- negation
   {ADD, Expr, Expr}         -- addition
   {SUB, Expr, Expr}         -- subtraction
   {MUL, Expr, Expr}         -- multiplcation
   {DIV, Expr, Expr}         -- division
   {EQ, Expr, Expr}          -- equality comparison
   {NE, Expr, Expr}          -- inequality comparison
   {LT, Expr, Expr}          -- less than comparion
   {GT, Expr, Expr}          -- greater than comparion
   {LE, Expr, Expr}          -- less or equal comparison
   {GE, Expr, Expr}          -- greater or equal comparison
   {IF, Expr, Expr, Expr}    -- if-then-else expression
                             -- (returns e2 value if e1 true
                             --  otherwise, returns e3 value)
   {MIN, Expr, Expr}         -- minimum value
   {MAX, Expr, Expr}         -- maximum value

Public constructor and type query functions for the abstract syntax
objects:

   Int, isInt -- integer number constants
   Var, isVar -- variable names
   Neg, isNeg -- negation
   Add, isAdd -- addition
   Sub, isSub -- subtraction
   Mul, isMul -- multiplication
   Div, isDiv -- division
   Eq,  isEQ  -- equality comparison
   Ne,  isNe  -- inequality comparison
   Lt,  isLt  -- less than comparison
   Gt,  isGt  -- greater than comparison
   Le,  isLt  -- less or equal comparison
   Ge,  isGt  -- greater or equal comparison
   If,  isIf  -- if-then-else expression
   Min, isMin -- minimum value
   Max, isMax -- maximun value

Public operand accessor function:   getArg

Public string conversion function:  exprToString

Internal:  isExpr, newBinOp, EXPRFIELDS, all type tag constants

--]]

-- Singleton constants to represent Expression type tags

local INT,   VAR,   NEG,   ADD,   SUB,   MUL,   DIV   =
      "Int", "Var", "Neg", "Add", "Sub", "Mul", "Div"
local EQ,   NE,   LT,   GT,   LE,   GE,   IF, MIN, MAX   =
      "Eq", "Ne", "Lt", "Gt", "Le", "Ge", "If", "Min", "Max"

-- Constant mapping from Expression type tags to required number of
-- arguments.

local EXPRFIELDS = {
   ["Int"] = 1, ["Var"] = 1, ["Neg"] = 1, 
   ["Add"] = 2, ["Sub"] = 2, ["Mul"] = 2, ["Div"] = 2,
   ["Eq"]  = 2, ["Ne"]  = 2, ["Lt"]  = 2, ["Gt"]  = 2,
   ["Le"]  = 2, ["Gt"]  = 2, ["If"]  = 3, ["Min"] = 2,
   ["Max"] = 2 
}

-- Internal query function "isExpr" checks whether the first level of
-- the data structure "e" has a valid Expression tag and number of
-- arguments. It does not recursively check arguments that are
-- Expressions.

local function isExpr(e, t)
   return type(e) == "table" and EXPRFIELDS[e[1]] == #e-1 and
      (t == nil or e[1] == t)
end

-- Accessor function "getArg" returns argument "n" of Expression "e".

local function getArg(e, n)
   if 1 <= n and n <= EXPRFIELDS[e[1]] then
      return e[n+1]
   else
      error("Expression argument index " .. n ..
            " out of range for expression " .. show_data(e))
   end
end

-- Internal constructor function "newBinOp" builds Expressions for
-- operators with two Expression arguments. It is used by other
-- constructors.

local function newBinOp(tag, e1, e2)
   if EXPRFIELDS[tag] == 2 and isExpr(e1) and isExpr(e2) then
      return {tag, e1, e2}
   else
      error("Cannot construct binary operator " .. tag ..
	    " with arguments:" .. show_data(e1) ..
	    " and " .. show_data(e2))
   end
end

-- Public constructor and type check query functions for Expression
-- types.

local function Int(n)
   if type(n) == "number" then  -- could check integer? coerce?
      -- check: if type(n) == "number" and n == math.floor(n) then
      return {INT, n}  -- coerce: return {INT, math.floor(n)}
   else
      error("Cannot construct Int with nonnumeric argument: "
	    .. show_data(n))
   end
end

local function isInt(e)
   return isExpr(e, INT)
end

local function Var(n)
   if type(n) == "string" then -- other check?
      return {VAR, n}
   else
      error("Cannot construct Var called with unsupported name"
	       .. show_data(n))
   end
end

local function isVar(e)
   return isExpr(e, VAR) 
end

local function Neg(e)
   if isExpr(e) then
      return {NEG, e}
   else
      error("Cannot construct unary operator Neg with argument: "
	       .. show_data(e))
   end
end

local function isNeg(e)
   return isExpr(e, NEG) 
end

local function Add(e1, e2)
   return newBinOp(ADD, e1, e2)
end

local function isAdd(e)
   return isExpr(e, ADD)
end

local function Sub(e1, e2)
   return newBinOp(SUB, e1, e2)
end

local function isSub(e)
   return isExpr(e, SUB)
end

local function Mul(e1, e2)
   return newBinOp(MUL, e1, e2)
end

local function isMul(e)
   return isExpr(e, MUL)
end

local function Div(e1, e2)
   return newBinOp(DIV, e1, e2)
end

local function isDiv(e)
   return isExpr(e, DIV) 
end

local function Eq(e1, e2)
   return newBinOp(EQ, e1, e2)
end

local function isEq(e)
   return isExpr(e, EQ)
end

local function Ne(e1, e2)
   return newBinOp(NE, e1, e2)
end

local function isNe(e)
   return isExpr(e, NE)
end

local function Lt(e1, e2)
   return newBinOp(LT, e1, e2)
end

local function isLt(e) 
   return isExpr(e, LT)
end

local function Gt(e1, e2)
   return newBinOp(GT, e1, e2)
end

local function isGt(e)
   return isExpr(e, GT)
end

local function Le(e1, e2)
   return newBinOp(LE, e1, e2)
end

local function isLe(e) 
   return isExpr(e, LE)
end

local function Ge(e1, e2)
   return newBinOp(GE, e1, e2)
end

local function isGe(e)
   return isExpr(e, GE)
end

local function Min(e1, e2)          --New function Min
   return newBinOp(MIN, e1, e2)
end

local function isMin(e)
   return isExpr(e, MIN)
end

local function Max(e1, e2)          --New function Min
   return newBinOp(MAX, e1, e2)
end

local function isMax(e)
   return isExpr(e, MAX)
end

local function If(e1, e2, e3)
   if isExpr(e1) and isExpr(e2) and isExpr(e3) then 
      return {IF, e1, e2, e3}
   else
      error("Cannot construct ternary operator IF with arguments:  "
	       .. show_data(e1) .. " ; " .. show_data(e2) .. " ; " 
	       .. show_data(e3))
   end
end

local function isIf(e)
  return isExpr(e, IF)
end

-- Public accessor function "exprToString" converts Expression "e" to
-- a readable string format.

local function exprToString(e)
   if isInt(e) then
      return "Int(" .. tostring(getArg(e,1)) .. ")"
   elseif isVar(e) then
      return "Var(" .. tostring(getArg(e,1)) .. ")"
   elseif isExpr(e) then -- only has Expression arguments
      local strb = {}
      for i = 2, EXPRFIELDS[e[1]]+1 do
	 strb[#strb+1] = exprToString(e[i])
      end
      return e[1] .. "( " .. table.concat(strb, ", ") .. " )"
   else
      error("Not a valid Expression in exprToString: "
            .. show_data(e))
   end
end


--[[ ENVIRONMENTS

This layer encapsulates the Environment table, which maps variable
names to their values.

This design supports nested environments. That is not needed in the
simple Expression language, but it will been needed for more capabile
languages in the future.

Public constructor function:  newEnv
Public accessor functions:    findBindings, getVal
Public procedures/mutators:   assign, setVal
Debugging:                    dumpEnv

Internal:  isEnv, ENV, ENCLOSING

--]]

-- Singleton constant as "tag" for Environments
local ENV = "Env"

-- Constant to denote field used for nesting of environments.
local ENCLOSING = -1  -- key for enclosing environment pointer

-- Internal query function "isEnv" to check whether "env" has the
-- structure of an Environment.

local function isEnv(env)
   return type(env) == "table" and env[1] == ENV
end

-- Public constructor function "newEnv" constructs a new empty
-- environment frame enclosed (nested) within "env". If "env" is nil
-- or unspecified, it creates a new "outer" environment.

local function newEnv(env)
   local localEnv = {ENV}        -- new empty environment frame
   if isEnv(env) then
      localEnv[ENCLOSING] = env  -- enclosed within "env"
   end
   return localEnv
end

-- Public accessor function "findBinding" returns the environment
-- frame in which "s" is defined; else it returns nil.  The returned
-- value is "env" or an environment frame that encloses it.

local function findBinding(s,env)
   if not isEnv(env) then
      return nil
   elseif env[s] ~= nil then -- could be value "false"
      return env
   else
      return findBinding(s,env[ENCLOSING])
   end
end

-- Public procedure (mutator) "assign" sets name "n" to have value "v"
-- in environment frame "env".

local function assign(n,v,env)
   env[n] = v
end

-- Public side-effecting mutator function "setVal" searches for a
-- binding of name "n" in environment frame "env" or any enclosing
-- environment frame.  If "n" is bound, then "setVal" sets the value
-- to "v"; otherwise, it binds "n" to "v" in optional environment
-- frame "defenv". It also returns the value set. Parameter "defenv"
-- defaults to the same as parameter "env" if nil or not specified.

local function setVal(n,v,env,defenv)
   defenv = defenv or env
   local senv = findBinding(n,env) 
   if senv then
      assign(n,v,senv)
   elseif isEnv(defenv) then
      assign(n,v,defenv)
   else
      error("Cannot assign " .. tostring(n) .. " in environment "
            .. show_data(env) .. " or " .. show_data(defenv))
   end
   return v
end

-- Public accessor function "getVal" returns the value of name "n" in
-- the environment frame "env" or some enclosing environment frame; it
-- returns nil if not found.

local function getVal(n,env)
   local boundin = findBinding(n,env)
   return boundin and boundin[n]
end


-- Public procedure "dumpEnv" prints all bindings from the top of the
-- environment frame stack. The top is depth 1, which is the default
-- value for argument "depth". This procedure is intended for
-- DEBUGGING ONLY.

local function dumpEnv(env,depth)
   local depth = depth or 1
   print("Environment frame dump for stack level " .. tostring(depth))
   if isEnv(env) then
      for k,v in pairs(env) do
         if k ~= 1 and k ~= ENCLOSING then
            print(k,treeConcat(v))
         end
      end
      dumpEnv(env[ENCLOSING], depth+1)
   elseif env == nil then
      print("End of dump. No frame at depth " .. tostring(depth))
   else
      error("Invalid environment " .. show_data(env))
   end
end


--[[ VALUES

This layer encapsulates some of the values used in the interpreter.

This section will need modification for languages with richer sets of values than integers.

For example, the representation for the concepts false and true
differs from one language to another and likely differs from the
values used by Lua. The intentions of features FALSEVAL, TRUEVAL, 
isFalse, isTrue, and asBoolVal are to isolate the differences between Lua and how those are handled in the interpreted languages.

Public constants:            TRUEVAL, FALSEVAL
Public query functions:      isTrue, isFalse
Public conversion function:  asBoolVal

--]]

-- Public constants for true and false
local FALSEVAL = 0
local TRUEVAL  = 1

-- Public query functions

local function isFalse(v)
   return v == FALSEVAL
end

local function isTrue(v)
  return v ~= FALSEVAL
end

-- Public conversion function "asBoolVal" takes a Lua falsey or truthy
-- value and returns the corresponding value used in the interpreted
-- language (FALSEVAL or TRUEVAL).

local function asBoolVal(b) 
  if b then return TRUEVAL else return FALSEVAL end 
end
   

--[[ EXPRESSION EVALUATOR

--]]

local function eval(e, env)
   print("DEBUG: Calling eval with " .. exprToString(e))
   if isInt(e) then
      return getArg(e,1)
   elseif isVar(e) then
      return getVal(getArg(e,1), env)
   elseif isNeg(e) then
      return - eval(getArg(e,1), env)
   elseif isAdd(e) then
      return eval(getArg(e,1), env) + eval(getArg(e,2), env)
   elseif isSub(e) then
      return eval(getArg(e,1), env) - eval(getArg(e,2), env)
   elseif isMul(e) then
      return eval(getArg(e,1), env) * eval(getArg(e,2), env)
   elseif isDiv(e) then
      return eval(getArg(e,1), env) / eval(getArg(e,2), env)
   elseif isEq(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left == right)
   elseif isNe(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left ~= right)
   elseif isLt(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left < right)
   elseif isGt(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left > right)
   elseif isLe(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left <= right)
   elseif isGe(e) then
      local left  = eval(getArg(e,1), env)
      local right = eval(getArg(e,2), env)
      return asBoolVal(left >= right)
   elseif isIf(e) then
      local first  = eval(getArg(e,1), env)
      local second = eval(getArg(e,2), env)
      local third = eval(getArg(e,3), env)
      if first then 
      return second
      else 
      return third
   end
   elseif isMin(e) then
      local first  = eval(getArg(e,1), env)
      local second = eval(getArg(e,2), env)
      if first < second then 
      return first
      else
      return second
   end
   elseif isMax(e) then
      local first  = eval(getArg(e,1), env)
      local second = eval(getArg(e,2), env)
      if first > second then
      return first
      else
      return second
   end
   else
      error("Invalid expression in eval: " .. show_data(e))
   end
end


--[[ MAIN PROGRAM (some testing)

--]]

print("\nSTART")
local env = newEnv()
setVal("x",1,env)
setVal("y",2,env)
setVal("z",3,env)
dumpEnv(env)

print("\nTry getVals")
local x, y, z = getVal("x", env), getVal("y", env), getVal("z", env) 
print("x, y, z = " .. x .. ", " .. y .. ", " .. z)

print("\nTry Int")
local two = Int(2)
print("two = Int(2) : " .. exprToString(two))
local three = Int(3)
print("three = Int(3) : " .. exprToString(three))
print("eval(Int(2), env)) =   " .. tostring(eval(two, env)))
print("eval(Int(3), env)) = " .. tostring(eval(three, env)))

print("\nTry Var")
local vx  = Var("x")
print("vx = Var(x) : " .. exprToString(vx))
print("eval(vx, env) = " .. tostring(eval(vx, env)))

local vy  = Var("y")
print("vy = Var(y) : " .. exprToString(vy))
print("eval(vy, env) = " .. tostring(eval(vy, env)))

print("\nTry Neg")
local en = Neg(three)
print("en = Neg(Int(3)) : " .. exprToString(en))
print("eval(en, env)) = " .. tostring(eval(en, env)))

print("\nTry Add")
local ea = Add(three, two)
print("ea = Add(Int(3),Int(2)) : " .. exprToString(ea))
print("eval(ea, env)) = " .. tostring(eval(ea, env)))

print("\nTry Sub")
local esub = Sub(three, en)
print("esub = Sub(three, en) : " .. exprToString(esub))
print("eval(esub, env)) = " .. tostring(eval(esub, env)))

print("\nTry Mul")
local emul = Mul(three, two)
print("emul = Mul(three, two) : " .. exprToString(emul))
print("eval(emul, env)) = " .. tostring(eval(emul, env)))

print("\nTry Div")
local ediv = Div(three, two)
print("ediv = Div(three, two) : " .. exprToString(ediv))
print("eval(ediv, env)) = " .. tostring(eval(ediv, env)))

print("\nTry Eq")
local ceq = Eq(three,three)
print("ceq = Eq(Int(3),Int(3)) : " .. exprToString(ceq))
print("eval(ceq, env) : " .. tostring(eval(ceq)))
ceq = Eq(two,three)
print("ceq = Eq(Int(2),Int(3)) : " .. exprToString(ceq))
print("eval(ceq, env) = " .. tostring(eval(ceq)))

print("\nTry If")
local eif = If(Eq(two,three), Var("x"), Var("y") )
print('eif = If(Eq(two,three), Var("x"), Var("y")) ' ..
      exprToString(eif))
print("eval(eif,env) = " .. tostring(eval(eif,env)))

print("\nTry min")
local cmin = Min(two,three)
print("cmin = Min(Int(2),Int(3)) : " .. exprToString(cmin))
print("eval(cmin, env) : " .. tostring(eval(cmin)))
print("\nTry max")
local cmax = Max(two,three)
print("cmax = Max(Int(2),Int(3)) : " .. exprToString(cmax))
print("eval(cmax, env) : " .. tostring(eval(cmax)))
print("\nEND")