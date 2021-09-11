import field
import quadratic_extension

inductive three_value : Type
  | zero : three_value
  | one  : three_value
  | two  : three_value

open three_value


def add : three_value -> three_value -> three_value
| zero x := x
| x zero := x
| one one := two
| one two := zero
| two one := zero
| two two := one

def mul : three_value -> three_value -> three_value
| zero _   := zero
| _ zero   := zero
| one x    := x
| two one  := two
| two two  := one

def negate : three_value -> three_value
| zero := zero
| one  := two
| two  := one

def reciprocal (x : three_value) (x_ne_zero : x ≠ zero) : three_value := x

lemma tv_add_comm (x y : three_value) : (add x y) = (add y x) :=
begin
  cases x, all_goals {cases y},
  all_goals {unfold add}, all_goals {unfold flip_bit}, all_goals {unfold id},
end

lemma tv_add_assoc (x y z : three_value) : (add x (add y z)) = (add (add x y) z) :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold add},
end

lemma tv_mul_comm (x y : three_value) : (mul x y) = (mul y x) :=
begin
  cases x, all_goals {cases y},
  all_goals {unfold mul},
end

lemma tv_mul_assoc (x y z : three_value) : (mul x (mul y z)) = (mul (mul x y) z) :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold mul}, all_goals {unfold mul},
end

lemma tv_add_zero (x : three_value) : x = (add x zero) :=
begin
  cases x, all_goals {unfold add},
end

lemma tv_mul_one (x : three_value) : x = (mul x one) :=
begin
  cases x, all_goals {unfold mul},
end

lemma tv_add_negate (x : three_value) : add x (negate x) = zero :=
begin
  cases x, all_goals {unfold negate, unfold add},
end

lemma tv_mul_reciprocal (x : three_value) (x_ne_zero : x ≠ zero) : mul x (reciprocal x x_ne_zero) = one :=
begin
  cases x, cc, all_goals {unfold reciprocal, unfold mul},
end

lemma tv_distrib (x y z : three_value) : add (mul x z) (mul y z) = mul (add x y) z :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold mul, unfold add}, all_goals {unfold mul},
end

lemma tv_zero_distinct_one : (one : three_value) ≠ (zero : three_value) := begin cc, end

instance gf3 :
  myfld three_value :=
{
  add := add,
  mul := mul,
  negate := negate,
  zero := zero,
  reciprocal := reciprocal,
  one := one,
  add_assoc := tv_add_assoc,
  mul_assoc := tv_mul_assoc,
  add_comm := tv_add_comm,
  mul_comm := tv_mul_comm,
  add_zero := tv_add_zero,
  mul_one := tv_mul_one,
  add_negate := tv_add_negate,
  mul_reciprocal := tv_mul_reciprocal,
  distrib := tv_distrib,
  zero_distinct_one := tv_zero_distinct_one,
}

lemma not_char_two : add one one ≠ zero := begin unfold add, cc, end

instance gf3_not_char_two :
  fld_not_char_two three_value := {not_char_two := not_char_two,}

/- We use x^2 + 1x + 2 = 0 as the example.
   The solution to this in this type is x = 1 + 2rt(2).-/

lemma quadratic_example : quadratic_subst_ips three_value _ one two 
                                              (quadratic_formula three_value one two) = 
                          ips_zero three_value _ :=
begin
  apply quadratic_formula_works,
end