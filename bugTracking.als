module bugTracking

open util/ordering[Dia] as do
open util/ordering[Codigo] as co

sig Dia {
	revisao : one Codigo,
	identificado: set Bug,
	correcao :	 set Codigo,
	corrigido : set Bug
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

-- cada relatorio so pertence a um bug
fact {
	all r:Relatorio | one r.~relatorio
}

--cada bug so pertence a um codigo
fact {
	all b:Bug | one b.~bugs
}

-- no primeiro dia a equipe de correção não tem o que fazer (nenhum bug foi ident. ainda)
-- a cada dia os bugs ident. pela eq. de revisao sao acrescentados à alocação do time de correção
-- e códigos já corrigidos saem da alocação do time de correção
fact {
	(do/first).correcao = none
	all d:Dia | d.correcao = (d.prev).correcao + (d.prev).revisao - d.corrigido.~bugs
}

-- os bugs encontrados em um dia tem de pertencer ao codigo sendo analisado naquele dia
-- e todo bug tem de estar nos identificados de algum dia
fact{
	all d:Dia, b:d.identificado | b = d.revisao.bugs - d.corrigido
	all b:Bug | b in Dia.identificado
}

-- na nossa instância, a equipe de correcao resolve os bug em 2 dias (dentro de uma semana) pra
-- facilitar a visualização e diminuir o escopo necessário
fact{
	(do/first).corrigido = none
	all d:Dia | d.corrigido = (d.prev).corrigido + (d.prev.prev).correcao.bugs
}

-- o time nao pode trabalhar dois dias consecutivos para um mesmo cliente
-- o codigo a ser revisado é o mais recente daquele cliente
-- codigos em correcao nao devem ser revisados
fact {
	all d:Dia | cliente[d.revisao] != cliente[(d.next).revisao]
	all d:Dia | d.revisao = last[codigos[cliente[d.revisao]] - d.correcao]
}

-- checa se um dado projeto possui bugs
pred temBug[p:Projeto]{
	#(p.raiz.subPastas.codigo.bugs) > 0
}

-- checa se a equipe de revisão encontrou bugs em um determinado dia
pred sucessoRevisao[d:Dia]{
	#(d.identificado) > 0
}

-- checa se a equipe de desenvolvimento corrigiu bugs em um determinado dia
pred sucessoCorrecao[d:Dia]{
	#(d.corrigido) > 0
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

-- encontra a versão mais recente entre um conjunto de códigos
fun last[c:Codigo] : one Codigo {
	c - c.^prev
}

-- acha a versao do codigo mais recente para um dado cliente
fun lastC[c:Cliente] : one Codigo{
	codigos[c] - codigos[c].^prev
}

-- checa que nenhum codigo pode ser revisado enquanto ainda está sendo corrigido
assert semDuplaAlocacao{
	all d:Dia, b:d.revisao | b not in d.correcao
}

check semDuplaAlocacao for 10 but 15 Dia

-- checa que nenhum codigo pode pertencer a mais de um cliente
-- justifica o uso do one no retorno da fun cliente
assert umClientePorCodigo{
	all c:Codigo | #c.~codigo.~subPastas.~raiz.~projetos = 1
}

check umClientePorCodigo for 10 but 15 Dia

-- checa se a equipe de revisão tem trabalho todos os dias
assert revisaoOcupada{
	all d:Dia | #d.revisao > 0
}

check revisaoOcupada for 10 but 15 Dia

pred show[]{
	--#Cliente = 2
}

run show for 10 but 15 Dia
