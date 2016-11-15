module language/grandpa1

abstract sig Person {
  father: lone Man,
  mother: lone Woman
}

sig Man extends Person {
  wife: lone Woman
}

sig Woman extends Person {
  husband: lone Woman
}

fact {
  no p: Person | p in p.^(mother + father)
  wife = ~husband
}

assert NoSelfFather {
  no m: Man | m = m.father
}
check NoSelfFather

fun grandpas(p: Person): set Person {
  p.(mother + father).father
}

pred ownGrandpa(p: Person) {
  p in grandpas [p]
}
run ownGrandpa for 4 Person

assert ownGranpa2 {
	lone p: Person | p in grandpas [p]
}
check ownGranpa2
