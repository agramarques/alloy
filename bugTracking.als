module bugTracking

open util/ordering[Time] as to

sig Time {
}

sig Repositorio {
	clientes: set Cliente
}

sig Cliente {
	projetos: some Projeto
}

sig Projeto {
	raiz: one Pasta
}

sig Pasta {
	subPastas: set SubPasta,
}

sig SubPasta {
	codigo: one Codigo
}

sig Codigo {
	bugs: set Bug
}

sig Bug {
	relatorio: one Relatorio,
	gravidade: Int
}{
gravidade > 0
gravidade <= 3
}

sig Relatorio {
}

fact {
	all c: Cliente | lone c.~clientes
}

-- cada projeto so pertence a um cliente:
fact {
	all p: Projeto | one p.~projetos
}

-- cada subpasta so pertence a uma pasta
fact {
	all s:SubPasta | one s.~subPastas
}

-- cada Pasta so e raiz de um projeto
fact {
	all p:Pasta | one p.~raiz
}

-- cada codigo so esta em uma subpasta
fact {
	all c:Codigo | one c.~codigo
}

-- cada relatoria so pertence a um bug
fact {
	all r:Relatorio | one r.~relatorio
}

--cada bug so pertence a um codigo
fact {
	all b:Bug | one b.~bugs
}

pred addCliente[r, r': Repositorio, c:Cliente]{
	r'.clientes = r.clientes + c
}

pred temBug[p:Projeto]{
	#(p.raiz.subPastas.codigo.bugs) > 0
}

-- função pra achar os projetos que tem bugs
fun bugados[]: set Projeto{
	Bug.~bugs.~codigo.~subPastas.~raiz
}

-- ver como lidar com o tempo (dias) e ordenar por tempo, pra pegar o mais recente

pred showAdd[r, r': Repositorio, c:Cliente]{
	r != r'
	addCliente[r,r',c]
	#Repositorio = 2
}

pred show[]{
--	#Cliente = 2
}

run showAdd for 3 but 2 Repositorio
