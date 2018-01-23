/*
 *
 * 	Elaborato K-FRAMEWORK per il corso di LINGUAGGI - UniVR
 *
 *	PENZO MICHELE - PIEROPAN EDOARDO
 *
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
	rule <k> ( Q, Qs:States => Qs ) ... </k> 
		 <states> S:Set => S SetItem(Q) </states>

	rule <k> .States => .K ... </k>

    /*
	 * Lettura dello stato finale, e viene messo il .K per dire che non c'è altro da leggere.
	 * Viene effettuato il controllo dove lo stato finale deve appartenere agli stati inseriti
	 * all'inizio del file.
     */
	rule <k> (Final: I1:Int => .K) ...  </k>
		<final-state> _ => I1 </final-state>
	 	<states> S:Set </states>
	 	when (I1 in S)

    /*
     * Inizializzazione dello stato iniziale e dello stato corrente
	 * Lo stato iniziale deve appartenere agli stati inseriti all'inizio del file.
     */
	rule <k> (Initial: I1:Int => .K) ...  </k>
     	<initial-state> _ => I1 </initial-state>
     	<current-state> _ => I1 </current-state>
		<states> S:Set </states>
	 	when (I1 in S)
		

	/*
	 * Caricamento nella mappa dei valori del nastro, ed aumento del valore della posizione corrente
	 * che viene associata come chiave al valore del nastro
	 * 
	 * Viene inoltre effettuato il controllo sulla lunghezza dei caratteri, devono essere caratteri
	 * e non delle stringhe
	 */
    rule <k> ... ( C, Crs:InitialTape => Crs ) ... </k>
	    <tape> Tape:Map => Tape[P <- C] </tape>
        <current-position> P:Int => P +Int 1 </current-position>
		when (lengthString(C) ==Int 1)

	/*
	 * Vengono poi caricate tutte le transizioni all'interno di una mappa apposita, quando viene caricata
	 * una transizione viene 'scritto' il valore "esecuzione" che identifica, per ogni sua scrittura,
	 * quante sono le transizioni che devono essere eseguite.
	 * Le chiavi delle transizioni sono come sopra definite, nella sintassi di K, come anche il valore che
	 * viene salvato.
	 *
	 * Vengono effettuati dei controlli, nel caso in cui gli stati sulla transizione appartengano agli stati
	 * definiti all'inizio del file, e che il carattere in input e quello in output siano effettivamente dei
	 * caratteri e non delle stringhe.
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
	 *
	 * Per quanto riguarda ogni movimento (L, R, -) della testina sul nastro sono state ripetute le varie operazioni,
	 * nel caso in cui ci sia : l'asterisco nel nastro
	 *							nella configurazione della tranzione
	 *							oppure che non ci sia.
	 *
	 */

	// Per RIGHT
		rule <k> .K </k>
			<transitions> ... (Cs, In) |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( In =/=String "*" )
	
		// fuori nastro RIGHT
		rule <k> .K </k>
			<transitions> ... (Cs,"*") |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(?Tape)))


		rule <k> .K </k>
			<transitions> ... (Cs, "*") |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( In ==TapeChar "*" )

		rule <k> .K </k>
			<transitions> ... (Cs, _:String) |-> (Next:Int, Out:String, R ) ... </transitions>
			<current-position> Cp:Int => Cp +Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( "*" ==TapeChar In )

	// Per LEFT
		rule <k> .K </k>
			<transitions> ... (Cs, In) |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( In =/=String "*" )

		// fuori nastro LEFT
		rule <k> .K </k>
			<transitions> ... (Cs,"*") |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(?Tape)))

		rule <k> .K </k>
			<transitions> ... (Cs, "*") |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( In ==TapeChar "*" )

		rule <k> .K </k>
			<transitions> ... (Cs, _:String) |-> (Next:Int, Out:String, L ) ... </transitions>
			<current-position> Cp:Int => Cp -Int 1 </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( "*" ==TapeChar In )

	// Per -
		rule <k> .K </k>
				<transitions> ... (Cs, In) |-> (Next:Int, Out:String, - ) ... </transitions>
				<current-position> Cp:Int </current-position>
				<current-state> Cs:Int => Next </current-state>
				<tape> ... Cp |-> (In:String => Out) </tape>
				when ( In =/=String "*" )

		// fuori nastro -
		rule <k> .K </k>
			<transitions> ... (Cs,"*") |-> (Next:Int, Out:String, - ) ... </transitions>
			<current-position> Cp:Int </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> Tape:Map => Tape[Cp <- Out] </tape>
			when (notBool(Cp in keys(?Tape)))

		rule <k> .K </k>
			<transitions> ... (Cs, "*") |-> (Next:Int, Out:String, - ) ... </transitions>
			<current-position> Cp:Int </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( In ==TapeChar "*" )

		rule <k> .K </k>
			<transitions> ... (Cs, _:String) |-> (Next:Int, Out:String, - ) ... </transitions>
			<current-position> Cp:Int </current-position>
			<current-state> Cs:Int => Next </current-state>
			<tape> ... Cp |-> (In:String => Out) </tape>
			when ( "*" ==TapeChar In )


    /*
	 * Equals with tape chars
	 */
	syntax Bool ::= K "==TapeChar" K [function]
	rule "*" ==TapeChar S:String => true
	rule S:String ==TapeChar "*" => true
	rule S1:String ==TapeChar S2:String => S1 ==String S2 when S1 =/=String "*" andBool S2 =/=String "*"

endmodule