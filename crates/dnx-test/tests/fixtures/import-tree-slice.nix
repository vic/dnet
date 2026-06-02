# import-tree gate SLICE — a nix-unit-style suite in the same shape as
# ~/hk/import-tree/tests.nix (nested attrset groups, `{ expr; expected; }`
# cases, dotted-path ids), restricted to the eval subset `dnx test` supports
# today (dnx-test-runner-design.md §8). Every case here is verified to evaluate
# on the dnx reducer; the upstream import-tree cases that DON'T fit (path
# literals, <nixpkgs/lib>, recursion, evalModules, expectedError) are catalogued
# in vic/notes/import-tree-gate-results.md as the honest blocker list.
#
# Discovery is structural (suite.rs): an attr with both `expr` and `expected`
# is a CASE; any other attrset is a GROUP walked recursively.
{
  arithmetic = {
    testAdd = { expr = 1 + 2; expected = 3; };
    testConv = { expr = 2 + 2; expected = 4; };
    testPrecedence = { expr = 1 + 2 * 3; expected = 7; };
    testSub = { expr = 10 - 4; expected = 6; };
    testMul = { expr = 6 * 7; expected = 42; };
    testIntDiv = { expr = 7 / 2; expected = 3; };
    testFloat = { expr = 3.0 + 0.5; expected = 3.5; };
  };

  strings = {
    testCat = { expr = "foo" + "bar"; expected = "foobar"; };
    testCat3 = { expr = "a" + "b" + "c"; expected = "abc"; };
    testEmpty = { expr = "" + "nonempty"; expected = "nonempty"; };
    testLength = { expr = builtins.stringLength "hello world"; expected = 11; };
    testLengthExpr = { expr = builtins.stringLength ("x" + "yz"); expected = 3; };
  };

  conditionals = {
    testThen = { expr = if true then 1 else 2; expected = 1; };
    testElse = { expr = if 2 > 5 then 1 else 99; expected = 99; };
    testCmp = { expr = if 1 < 2 then "y" else "n"; expected = "y"; };
    testNested = { expr = "result: " + (if 3 > 2 then "yes" else "no"); expected = "result: yes"; };
  };

  comparison = {
    testIntEq = { expr = 1 == 1; expected = true; };
    testIntNeq = { expr = 1 == 2; expected = false; };
    testStrEq = { expr = "x" == "x"; expected = true; };
    testLt = { expr = 3 < 4; expected = true; };
  };

  bindings = {
    testLet = { expr = let x = 5; in x + 1; expected = 6; };
    testLetMulti = { expr = let x = 10; y = 20; in x * y; expected = 200; };
    testLambda = { expr = (x: x + 1) 41; expected = 42; };
    testLambdaSelf = { expr = let f = x: x * x; in f 9; expected = 81; };
    testCurried = { expr = let g = a: b: a - b; in g 10 3; expected = 7; };
  };

  attrsets = {
    testSelect = { expr = { a = 1; b = 2; }.b; expected = 2; };
    testSelectNested = { expr = { a = { b = 3; }; }.a.b; expected = 3; };
    testSelectArith = { expr = { a = 5; b = 6; }.a * 2; expected = 10; };
    testLetSelect = { expr = let xs = { one = 1; two = 2; }; in xs.two + 100; expected = 102; };
    testHasTrue = { expr = { a = 1; } ? a; expected = true; };
    testHasFalse = { expr = { a = 1; b = 2; } ? c; expected = false; };
  };

  builtins-introspect = {
    testTypeInt = { expr = builtins.typeOf 5; expected = "int"; };
    testTypeStr = { expr = builtins.typeOf "s"; expected = "string"; };
    testTypeBool = { expr = builtins.typeOf true; expected = "bool"; };
    testTypeNull = { expr = builtins.typeOf null; expected = "null"; };
    testTypeOfExpr = { expr = builtins.typeOf (1 + 2); expected = "int"; };
    testIsInt = { expr = builtins.isInt 5; expected = true; };
    testIsString = { expr = builtins.isString "x"; expected = true; };
    testIsNull = { expr = builtins.isNull null; expected = true; };
  };

  # Convertibility, not literal identity: differently-written exprs that
  # normalize to the same net pass (the dnx-native equality, design §3).
  convertibility = {
    testArithConv = { expr = 3 * 3; expected = 4 + 5; };
    testStrConv = { expr = "ab" + "cd"; expected = "abc" + "d"; };
    testIfConv = { expr = if 10 > 1 then 2 + 2 else 0; expected = 4; };
  };
}
