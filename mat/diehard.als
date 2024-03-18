module diehard

open util/integer

// Hinweise von Peter Kriens und David Chemouil haben geholfen, diese
// Version zu entwickeln

abstract sig Jug {
	var gallons : Int,
	capacity : Int
}

one sig Jug3 extends Jug {}{ capacity = 3 }
one sig Jug5 extends Jug {}{ capacity = 5 }

/*
pred fill[j: Jug] {
	j.gallons' = j.capacity
	all unchanged : Jug-j | unchanged.gallons' = unchanged.gallons
}
besser: 

gallons ist eine Relation Jug x Int
j->j.capacity ist ein Tupel in dieser Relation (zum Jug j)
Der Operator ++ überschreibt das Tupel j->Zahl in gallons
*/
pred fill[j: Jug] {
	gallons' = gallons ++ j->j.capacity 
}

/*
pred empty[ j : Jug ] {
	j.gallons' = 0	
	all unchanged : Jug-j | unchanged.gallons' = unchanged.gallons
}
*/

pred empty[j: Jug] {
	gallons' = gallons ++ j->0 
}


/*
Wir können Umfüllen mit:
pred smallToBig {
	let amount = add[State.Big, State.Small] |
		int amount <= 5 implies		
			(State.Small' = 0 and State.Big' = amount)
		else
			(State.Big' = 5 and State.Small' = sub[State.Small, sub[5, State.Big]])
}
Das kann man aber auch anders machen:

Wir rechnen aus, wieviel wir umschütten:
Das ist alles, wenn es Platz hat, also from. gallons
oder was reinpasst d.h. to.capacity - to.gallons

also 
Man beachte, dass das + nicht die Addition ist, sondern die Mengenvereinigung
*/
pred pour[from, to: Jug] {
	let amount = min[to.capacity.minus[to.gallons] + from.gallons] {
		from.gallons' = from.gallons.minus[amount]
		to.gallons' = to.gallons.plus[amount]
	} 
}

// Startzustand
pred init {
	all j: Jug | j.gallons = 0
}

// Wie soll sich das System im  Laufe der Zeit verhalten?
fact traces {
	init
	always { 
		one j: Jug | fill[j] or empty[j] or pour[j, Jug-j] 
	}
}

// Wir müssen in Alloy nicht einen Widerspruchsbeweis machen wie in TLA+,
// sondern wir wollen uns einfach ein Beispiel erzeugen lassen, in dem
// wir 4 Gallonen im größeren Krug haben
run {
	eventually Jug5.gallons = 4
}


