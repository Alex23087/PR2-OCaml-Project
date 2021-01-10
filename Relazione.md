##Relazione

###Metodo di Sviluppo del Progetto
Il progetto è stato sviluppato unicamente con un editor di testo con syntax highlighting per OCAML, evitando l'uso di strumenti esterni. Per eseguire il progetto con tutti i test è sufficiente passare il file dei test come argomento all'interprete ocaml:

```bash
ocaml tests.ml
```

###Overview Generale sul Progetto e Scelte di Implementazione
La consegna del progetto richiedeva di estendere il linguaggio funzionale presentato a lezione col tipo di dato `Set` e una serie di operazioni su di esso. Il tipo `Set` è stato realizzato come tipo ricorsivo, ossia è possibile esprimere `Set` di `Set`, e così via.
È stato inoltre deciso di estendere il linguaggio con altre funzionalità, come quella di avere funzioni a più parametri, funzioni ricorsive, e con l'espressione `Print`.\
Essendo le funzioni ricorsive non il punto focale del progetto, si è deciso di implementarle creando un binding tra l'identificatore riservato `rec` e la `Closure` della funzione stessa, il che ha anche il vantaggio di rendere banale creare una funzione anonima ricorsiva.\
L'espressione `Print` è stata realizzata come espressione che restituisce il valore passato come parametro, col side effect di stamparlo a schermo, in modo tale da non dover introdurre meccanismi per la programmazione imperativa.


###Type checking
È stato innanzitutto scelto di aggiungere informazioni di tipo sia dei parametri in input che in output per le funzioni, in modo da poter eseguire controlli di tipo più approfonditi (ad es. controllare che in un insieme tutte le funzioni abbiano lo stesso tipo `T1 * T2... -> Tr`; o ancora per controllare che il predicato passato ad una `Forall` su un set di tipo `Set(T)` sia di tipo `T -> Boolean`)\
Il progetto comprende sia un meccanismo di type checking dinamico, utilizzato direttamente dalla funzione di valutazione delle espressioni, sia una funzione di type checking statico.


###Tests
I test sono stati sviluppati in modo da testare tutte le espressioni disponibili nel linguaggio, e da verificare che per ognuna di esse vengano restituiti i valori corretti per parametri corretti, e che siano lanciate le `Exceptions` corrette per valori illegali.
