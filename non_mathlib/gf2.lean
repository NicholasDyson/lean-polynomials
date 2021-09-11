import field

inductive two_value : Type
  | zero : two_value
  | one  : two_value

open two_value

def flip_bit : two_value -> two_value
| zero := one
| one  := zero

def add : two_value -> two_value -> two_value
| zero zero := zero
| zero one := one
| one zero := one
| one one := zero

def mul : two_value -> two_value -> two_value
| zero _   := zero
| _ zero   := zero
| one one  := one

def reciprocal (x : two_value) (x_ne_zero : x ≠ zero) : two_value := one

lemma tv_add_comm (x y : two_value) : (add x y) = (add y x) :=
begin
  cases x, all_goals {cases y},
  all_goals {unfold add}, all_goals {unfold flip_bit}, all_goals {unfold id},
end

lemma tv_add_assoc (x y z : two_value) : (add x (add y z)) = (add (add x y) z) :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold add},
end

lemma tv_mul_comm (x y : two_value) : (mul x y) = (mul y x) :=
begin
  cases x, all_goals {cases y},
  all_goals {unfold mul},
end

lemma tv_mul_assoc (x y z : two_value) : (mul x (mul y z)) = (mul (mul x y) z) :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold mul}, all_goals {unfold mul},
end

lemma tv_add_zero (x : two_value) : x = (add x zero) :=
begin
  cases x, all_goals {unfold add},
end

lemma tv_mul_one (x : two_value) : x = (mul x one) :=
begin
  cases x, all_goals {unfold mul},
end

lemma tv_add_negate (x : two_value) : add x (id x) = zero :=
begin
  cases x, all_goals {unfold id, unfold add},
end

lemma tv_mul_reciprocal (x : two_value) (x_ne_zero : x ≠ zero) : mul x (reciprocal x x_ne_zero) = one :=
begin
  cases x, cc, unfold reciprocal, unfold mul,
end

lemma tv_distrib (x y z : two_value) : add (mul x z) (mul y z) = mul (add x y) z :=
begin
  cases x, all_goals {cases y}, all_goals {cases z},
  all_goals {unfold mul, unfold add}, all_goals {unfold mul},
end

lemma tv_zero_distinct_one : (one : two_value) ≠ (zero : two_value) := begin cc, end

instance gf2 :
  myfld two_value :=
{
  add := add,
  mul := mul,
  negate := id,
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