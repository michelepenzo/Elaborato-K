/*
 *
 * 	Elaborato K-FRAMEWORK per il corso di LINGUAGGI - UniVR
 *
 *	PENZO MICHELE - PIEROPAN EDOARDO
 *	
 *	I FILE DI PROVA SONO I SEGUENTI:
 *	- example_1.mdt -> riconosce una stringa contente tre a consecutive, del linguaggio L={a,b} (es. aaaba)
 *	- example_2.mdt -> inverte gli zeri con uni e viceversa
 *	- example_3.mdt -> somma 1 al valore binario inserito nel tape 
 */

module MDT-SYNTAX

	/*
	 * TM states, lista degli stati della mdt
	 */
	syntax States ::= List{Int, ","}

	/*
	 * TM Final state declaration, stato finale (solamente 1)
	 */
	syntax FinalState ::= "Final" ":" Int

	/*
	 * TM Initial state declaration, stato iniziale (solamente 1)
	 */
	syntax InitialState ::= "Initial" ":" Int

	/*
	 * Configurazione del movimento della testina, left right or nothing
	 */
	syntax Movement ::= "L" | "R" | "-"

	/*
	 * TM Transitions declaration, definizione della transizione. Inoltre una transizione è definita come due transizioni
	 *
	 * stato corrente , simbolo di input, stato successivo, simbolo di output, SPOSTAMENTO
	 *
	 */
	
	syntax Transition ::= "(" Int "," String "," Int "," String "," Movement ")"
						| Transition Transition [left]							// transizione concatenata ad un altra

	/*
	 * Initial tape declaration, definizione del nastro, ovvero tutte le sequenze di simboli che deve eseguire
	 */
	syntax InitialTape ::= List{String, ","}

	/*
	 * Un programma è cosi definito, con le seguenti definizioni
	 */
	syntax Program ::= States FinalState InitialState Transition InitialTape

endmodule


module MDT
	imports MDT-SYNTAX

	/*
	 * transitions-configuration map key
	 */
	syntax K ::= "(" Int "," String ")"

	/*
	 * transitions-configuration map value
	 */
	syntax K ::= "(" Int "," String "," Movement ")"

	configuration
	<T>
		<k> $PGM:Program </k>
		<tape> .Map </tape>
		<current-state> 0 </current-state>
		<current-position> 0 </current-position>
		<transitions> .Map </transitions>
		<states> .Set </states>
		<final-state> 0 </final-state>				/* messi a zero per inizializzare il valore dello stato iniziale e finale */
		<initial-state> 0 </initial-state>
	</T>

	/*
	 * ~> indica l'ordine di valutazione
	 */
	rule SI:States F:FinalState I:InitialState TT:Transition Tape:InitialTape
		=> SI ~> F ~> I ~> TT ~> Tape [structural]

	/*
	 * valuta l'ordine delle transizioni, una transizione può essere concatenata da un'altra transizione
	 */
	rule T1:Transition T2:Transition => T1 ~> T2 [structural]

	/*
	 * Q e Qs 'appartengono' entrambi a States
	 * Q è lo stato attuale, mentre Qs è lo stato prossimo
	 */
	rule <k> ( Q, Qs:States => Qs ) ... </k> 		// 1 2 3 4 5
		 <states> S:Set => S SetItem(Q) </states>

	rule <k> .States => .K ... </k>

    /*
     * leggo finalstate da Program, lo "svuoto" e inserisco in <finalstate> il valore letto
     */
	rule <k> (Final: I1:Int => .K) ...  </k>
		<final-state> _ => I1 </final-state>
	 	<states> S:Set </states>
	 	when (I1 in S)

    /*
     * Inizializzazione dello stato iniziale e dello stato corrente
     */
	rule <k> (Initial: I1:Int => .K) ...  </k>
     	<initial-state> _ => I1 </initial-state>
     	<current-state> _ => I1 </current-state>
		<states> S:Set </states>
	 	when (I1 in S)
		

	/*
	 * Caricamento nella mappa dei valori del nastro, ed aumento del valore della posizione corrente
	 * che viene associata come chiave al valore del nastro
	 */
    rule <k> ... ( C, Crs:InitialTape => Crs ) ... </k>
	    <tape> Tape:Map => Tape[P <- C] </tape>
        <current-position> P:Int => P +Int 1 </current-position>
		when (lengthString(C) ==Int 1)

	/*
	 * Vengono poi caricate tutte le transizioni all'interno di una mappa apposita.
	 * Le chiavi delle transizioni sono come sopra definite, nella sintassi di K, come anche il valore che
	 * viene salvato
	 */
	rule <k> ... ((I:Int, C:String, I2:Int, C2:String, M:Movement)) => .K ... </k>
        <transitions> Trs:Map => Trs[(I, C) <- (I2, C2, M)] </transitions>
		<states> S:Set </states>
	 	when ((I in S) andBool (I2 in S) andBool (lengthString(C) ==Int 1) andBool (lengthString(C2) ==Int 1))

	/*
	 * Dopo che il nastro è stato completamente 'letto' il valore della posizione corrente viene inizializzato
	 * a 0, questo indica che si può iniziare cone l'esecuzione delle transizioni
	 */
    rule <k> ... .InitialTape => .K ... </k>
         <current-position> _ => 0 </current-position>

	/*
	 * Esecuzione delle transizioni, in questo caso vengono eseguite le transizioni con il movimento verso destra,
	 * quindi la posizione correte deve essere aumentata di 1 e lo stato deve essere quello che è stato letto
	 * dalla transizione in mapppa.
	 */

	// Per RIGHT 
		// Con Input un valore qualsiasi
		rule <k> .K </k>
			<transitions> ... (Cs, In1:String) |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In2:String => Out) </tape>
			when ( In1 ==TapeChar In2 andBool (Cp in keys(?Tape)))

		// Fuori nastro
		rule <k> .K </k>
			<transitions> ... (Cs,In1:String) |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(Tape)) andBool In1 ==TapeChar "_")

	// Per LEFT 
		// Con In un valore qualsiasi
		rule <k> .K </k>
			<transitions> ... (Cs, In1:String) |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In2:String => Out) </tape>
			when ( In1 ==TapeChar In2 andBool (Cp in keys(?Tape)))

		// Fuori nastro
		rule <k> .K </k>
			<transitions> ... (Cs,In1:String) |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(Tape)) andBool In1 ==TapeChar "_")

	// Per NOTHING 
		// Con In un valore qualsiasi
		rule <k> .K </k>
			<transitions> ... (Cs, In1:String) |-> (Next:Int, Out:String, - ) ... </transitions>
			<current-position> Cp:Int </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In2:String => Out) </tape>
			when ( In1 ==TapeChar In2 andBool (Cp in keys(?Tape)))

		// Fuori nastro
		rule <k> .K </k>
			<transitions> ... (Cs,In1:String) |-> (Next:Int, Out:String, - ) ... </transitions>
			<current-position> Cp:Int </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(Tape)) andBool In1 ==TapeChar "_")

    /*
	 * Equals with tape chars
	 */
	syntax Bool ::= K "==TapeChar" K [function]
	rule "*" ==TapeChar S:String => true
	rule S:String ==TapeChar "*" => true
	rule S1:String ==TapeChar S2:String => S1 ==String S2 when S1 =/=String "*" andBool S2 =/=String "*"

endmodule