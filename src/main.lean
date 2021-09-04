import system.io

namespace Turing
open list

inductive Direction
  | Left
  | Right
  | Stay

notation `State` := ℕ
notation `Symbol` := char
structure Smt :=
  mk :: (fst: State) (snd: Symbol) (trd: Direction)
--notation `Smt` := State × Symbol × Direction
notation `Tape` := list Symbol
structure TapeParts :=
  mk :: (fst: Tape) (snd: Symbol) (trd: Tape)
--notation `TapeParts` := Tape × Symbol × Tape
-- (a : State) (b : State → Symbol → Smt) (c : State)
structure Machine :=
  mk :: (init_state: State) 
        (function: State → Symbol → Smt) 
        (accept_state: State)

structure MacState :=
  mk :: (state: State) 
        (tape: TapeParts)

def moveTape : TapeParts → Direction → TapeParts
  | (TapeParts.mk [] b c) Direction.Left := TapeParts.mk [] '_' (b :: c)
  | (TapeParts.mk a b []) Direction.Right := TapeParts.mk (a ++ [b]) '_' []
  | (TapeParts.mk a b c) Direction.Left := TapeParts.mk (init a) (ilast a) (b :: c)
  | (TapeParts.mk a b c) Direction.Right := TapeParts.mk (a ++ [b]) (head c) (tail c)
  | a Direction.Stay := a


/- We are giving a number big enough, so we assure the program ends. -/
def step : ℕ → Machine → TapeParts → list MacState → list MacState
  | 0 (Machine.mk q0 f qf) (TapeParts.mk a b c) mac := []
  | (nat.succ n) (Machine.mk q0 f qf) (TapeParts.mk a b c) mac :=
    if q0 ≥ qf ∧ qf ≤ q0 then
      mac ++ [MacState.mk q0 (TapeParts.mk a b c)] else
      let (Smt.mk x y z) := f q0 b in
        step n (Machine.mk x f qf) (moveTape (TapeParts.mk a y c) z) (
        mac ++ [MacState.mk q0 (TapeParts.mk a b c)])

def run : Machine → Tape → list MacState
  | m t := step 1000000000000 m (TapeParts.mk [] (head t) (tail t)) []

def pTString : Tape → string
  | [] := ""
  | (x::xs) := to_string x ++ pTString xs

def machineState2String : list MacState → string
  | [] := ""
  | ((MacState.mk q (TapeParts.mk a b c))::xs) :=
    pTString a ++ " q_" ++ to_string q ++ " " ++ pTString c ++ "\n"
      ++ machineState2String xs 

end Turing

set_option trace.eqn_compiler.elim_match true
set_option eqn_compiler.max_steps 2147483647
def testMachineFn : State → Symbol → Turing.Smt
    | 0  '1' := Turing.Smt.mk 1  '_' Turing.Direction.Right
    | 0  '0' := Turing.Smt.mk 20 '_' Turing.Direction.Right
    | 1  '1' := Turing.Smt.mk 1  '1' Turing.Direction.Right
    | 1  '0' := Turing.Smt.mk 2  '0' Turing.Direction.Right
    | 2  '1' := Turing.Smt.mk 2  'b' Turing.Direction.Right
    | 2  '_' := Turing.Smt.mk 3  '_' Turing.Direction.Left
    | 3  'b' := Turing.Smt.mk 3  'b' Turing.Direction.Left
    | 3  '1' := Turing.Smt.mk 3  '1' Turing.Direction.Left
    | 3  '0' := Turing.Smt.mk 4  '0' Turing.Direction.Right
    | 3  'a' := Turing.Smt.mk 4  'a' Turing.Direction.Right
    | 4  'b' := Turing.Smt.mk 5  'a' Turing.Direction.Right
    | 4  '1' := Turing.Smt.mk 6  'b' Turing.Direction.Right
    | 5  'b' := Turing.Smt.mk 5  'b' Turing.Direction.Right
    | 5  '_' := Turing.Smt.mk 3  '1' Turing.Direction.Left
    | 6  '1' := Turing.Smt.mk 6  'b' Turing.Direction.Right
    | 6  '_' := Turing.Smt.mk 7  '_' Turing.Direction.Left
    | 7  'a' := Turing.Smt.mk 7  'a' Turing.Direction.Left
    | 7  'b' := Turing.Smt.mk 7  'b' Turing.Direction.Left
    | 7  '0' := Turing.Smt.mk 8  '0' Turing.Direction.Left
    | 8  '1' := Turing.Smt.mk 8  '1' Turing.Direction.Left
    | 8  '_' := Turing.Smt.mk 0  '_' Turing.Direction.Right
    | 20 'a' := Turing.Smt.mk 20 '1' Turing.Direction.Right
    | 20 'b' := Turing.Smt.mk 20 '_' Turing.Direction.Right
    | 20 '_' := Turing.Smt.mk 30 '_' Turing.Direction.Stay
    | 5  '1' := Turing.Smt.mk 5  '1' Turing.Direction.Right
    | 2  'a' := Turing.Smt.mk 2  'a' Turing.Direction.Right
    | 2  'b' := Turing.Smt.mk 2  'b' Turing.Direction.Right
    | n  m := Turing.Smt.mk 70  m Turing.Direction.Stay /- Ensure this works
    in any case. -/

def testMachine : Turing.Machine
:= Turing.Machine.mk 0 testMachineFn 30

open io
def main : io unit := put_str (Turing.machineState2String (Turing.run testMachine ['1','1','1','1','1','1','1','1','0','1','1','1','1','1','1','1','1']
) )

#eval main