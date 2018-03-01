module bugTracking

open util/ordering[Dia] as do
open util/ordering[Codigo] as co

sig Dia {
	alocacao : one Codigo
}

one sig Repositorio {
	clientes: set Cliente
}

sig Cliente {
	projetos: some Projeto
}

sig Projeto {
	raiz: one Pasta
}

sig ProjetoBugado extends Projeto{
}

sig Pasta {
	subPastas: set SubPasta,
}

sig SubPasta {
	codigo: one Codigo
}

sig Codigo {
	bugs: set Bug,
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

-- todos (e somente) projetos bugados possuem bugs
fact {
	all b: ProjetoBugado | #b.raiz.subPastas.codigo.bugs > 0
	no p: (Projeto - ProjetoBugado) | #p.raiz.subPastas.codigo.bugs > 0
}

-- todo cliente deve pertencer ao repositorio
fact {
	all c: Cliente | one c.~clientes
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

-- o time nao pode trabalhar dois dias consecutivos para um mesmo cliente
fact {
	all d:Dia | cliente[d.alocacao] != cliente[(d.next).alocacao]
	all d:Dia | d.alocacao = lastC[cliente[d.alocacao]]
}

pred temBug[p:Projeto]{
	#(p.raiz.subPastas.codigo.bugs) > 0
}

-- funçao de comparação entre codigos pra realizar a ordenação do subconjunto (achar o mais recente por cliente)
fun maior[c1,c2 : Codigo] : one Codigo {
	(c1 in c2.^next) => c1 else c2
}
	
-- retorna o cliente que possui o codigo pra facilitar o acesso
fun cliente[c:Codigo] : one Cliente {
	c.~codigo.~subPastas.~raiz.~projetos
}

-- atalho para os codigos de um cliente
fun codigos[c:Cliente] : set Codigo {
	c.projetos.raiz.subPastas.codigo
}

-- função pra achar os projetos de um cliente que tem bugs
fun bugados[c:Cliente]: set Projeto{
	c.projetos & ProjetoBugado
}

-- acha a versao do codigo mais recente para um dado cliente
fun lastC[c:Cliente] : one Codigo{
	codigos[c] - codigos[c].^prev
}

pred show[]{
	--#Cliente = 2
}

run show for 5
