using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdSystem
{
    public class FolThresholdSystem
    {
        public const string EmptySetIdentifier = "EMPTYSET";
        public const string UniversalSetIdentifier = "UNIVERSALSET";

        public readonly Dictionary<string, Identifier> Identifiers = new Dictionary<string, Identifier>();
        public readonly List<Specification> Formulas = new List<Specification>();

        public FolThresholdSystem()
        {
            Identifiers[EmptySetIdentifier] = new Quorum(true, EmptySetIdentifier, SyntaxKind.EqualToken,
                new NatConstExpression(0));

            Identifiers[UniversalSetIdentifier] = new Quorum(true, UniversalSetIdentifier, SyntaxKind.EqualToken,
                new NatVarExpression("n"));

            Formulas.Add(new Specification
            {
                Conjecture = false,
                NaturalSpec = true,
                Formula = new NaturalFormula(new NatVarExpression("n"), SyntaxKind.GreaterThanToken, new NatConstExpression(0))
            });
        }

        public void ParseCode(Token[] tokens)
        {
            try
            {
                if (tokens.Length == 0) return;

                var identifier = Identifier.Parse(tokens);
                if (identifier != null)
                {
                    if (Identifiers.ContainsKey(identifier.Name))
                    {
                        throw new ParserTokenException("Multiple definitions of the same identifier", tokens[0]);
                    }

                    Identifiers[identifier.Name] = identifier;
                    return;
                }

                var formula = Specification.Parse(tokens);
                if (formula != null)
                {
                    Formulas.Add(formula);
                    return;
                }

                throw new Exception("Could not parse line");
            }
            catch (ParserTokenException)
            {
                throw;
            }
            catch (Exception ex)
            {
                throw new ParserTokenException("Illegal line", tokens[0], ex);
            }
        }

        public IEnumerable<string> ToIvyAxioms()
        {
            yield return "type node";
            foreach (var quorum in Identifiers.Values.OfType<Quorum>().Where(quo => !quo.Constant))
            {
                yield return $"type quorum_{quorum.Name.ToLower()} # {Tokenizer.Keywords[quorum.Operation]} {quorum.Expression}";
            }

            yield return string.Empty;

            foreach (var quorum in Identifiers.Values.OfType<Quorum>())
            {
                if (quorum.Constant) yield return $"relation member_{quorum.Name.ToLower()}(N:node)";
                else yield return $"relation member_{quorum.Name.ToLower()}(N:node, Q:quorum_{quorum.Name.ToLower()})";
            }

            yield return string.Empty;

            yield return $"axiom forall N:node. ~member_{EmptySetIdentifier.ToLower()}(N)";
            yield return $"axiom forall N:node. member_{UniversalSetIdentifier.ToLower()}(N)";

            yield return string.Empty;

            foreach (var formula in Formulas.Where(spec => spec.Conjecture))
            {
                yield return "axiom " + formula.ToBoundIvyAxiom(Identifiers);
            }
        }

        public IEnumerable<string> AssertThresholdSmt2(Specification conjecture)
        {
            var quorums = Identifiers.Values.OfType<Quorum>().Where(quorum => !quorum.Constant).ToList();

            yield return "(set-logic ALL_SUPPORTED)";
            yield return "(set-info :status unsat)";

            yield return string.Empty;

            yield return $"; {conjecture}";

            yield return string.Empty;

            // natural constant
            foreach (var quorum in Identifiers.Values.OfType<Natural>().Where(identifier => identifier.Constant))
            {
                yield return $"(declare-fun {quorum.Name} () Int)";
            }

            yield return string.Empty;

            // quorum constant
            foreach (var quorum in Identifiers.Values.OfType<Quorum>().Where(identifier => identifier.Constant))
            {
                yield return $"(declare-fun {quorum.Name} () (Set Int))";
            }

            yield return string.Empty;

            // axioms concerning constants
            foreach (var spec in Formulas.Where(spec => !spec.Conjecture))
            {
                yield return $"(assert {spec.Formula.GetSmtAssert(Identifiers, quorums)})";
            }

            // constant quorum thresholds
            foreach (var quorum in Identifiers.Values.OfType<Quorum>().Where(identifier => identifier.Constant))
            {
                yield return $"(assert (subset {quorum.Name} {UniversalSetIdentifier}))";
                var axiom = new NaturalFormula(new NatCardExpression(new SetVarExpression(quorum.Name)), quorum.Operation, quorum.Expression);
                yield return $"(assert {axiom.GetSmtAssert(Identifiers, quorums)})";
            }

            yield return string.Empty;

            var formula = conjecture.Formula.Negate();
            var boundVariables = formula.Release(FormulaBind.BindType.ExistsSet).ToList();

            // variables from conjecture
            foreach (var boundVar in boundVariables)
            {
                if (!Identifiers.ContainsKey(boundVar.VarType)) throw new Exception("Unknown variable");
                yield return $"(declare-fun {boundVar.VarName.ToUpper()} () (Set Int))";
                yield return $"(assert (subset {boundVar.VarName.ToUpper()} {UniversalSetIdentifier}))";

                var quorum = Identifiers[boundVar.VarType] as Quorum;
                if (quorum == null) throw new Exception("Expected quorum identifier");

                var axiom = new NaturalFormula(new NatCardExpression(new SetVarExpression(boundVar.VarName)), quorum.Operation, quorum.Expression);
                var tempIdentifiers = new Dictionary<string, Identifier>(Identifiers.Where(pair => pair.Value.Constant).ToDict())
                {
                    [boundVar.VarName] = Identifiers[boundVar.VarType]
                };
                yield return $"(assert {axiom.GetSmtAssert(tempIdentifiers, quorums)})";
                yield return string.Empty;
            }

            yield return string.Empty;
            
            yield return $"(assert {formula.GetSmtAssertActual(Identifiers, quorums)})";

            yield return string.Empty;

            yield return "(check-sat)";
            yield return "(get-model)";
        }

        public IEnumerable<Specification> ProduceConjectures()
        {
            var constantQuorums = Identifiers.Values.OfType<Quorum>().Where(quorum => quorum.Constant)
                .Where(quorum => quorum.Name != EmptySetIdentifier)
                .Where(quorum => quorum.Name != UniversalSetIdentifier).ToArray();
            var quorums = Identifiers.Values.OfType<Quorum>().Where(quorum => !quorum.Constant).ToArray();
            foreach (var sets in ProduceVarSet(constantQuorums, quorums))
            {
                foreach (var expr in VennDiagram.VennDiagramIterator.GetVennZonesHelper(sets.Item1))
                {
                    yield return new Specification
                    {
                        Conjecture = true,
                        NaturalSpec = false,
                        Formula = FormulaBind.Aggregate(sets.Item2, new SetFormula(expr, SetFormula.SetRelation.NotEuqal, new SetVarExpression(EmptySetIdentifier)))
                    };
                    foreach (var quorum in quorums)
                    {
                        yield return new Specification
                        {
                            Conjecture = true,
                            NaturalSpec = false,
                            Formula = FormulaBind.Aggregate(sets.Item2, new SetRelationFormula(expr, quorum.Name))
                        };
                    }
                }
            }
        }

        private IEnumerable<Tuple<SetVarExpression[], FormulaBind.Bind[]>> ProduceVarSet(Quorum[] constantQuorums, Quorum[] quorums)
        {
            for (var numberOfVars = 1; ; ++numberOfVars)
            {
                foreach (var tuple in ProduceVarSetHelper(constantQuorums, quorums, numberOfVars))
                {
                    yield return tuple;
                }
            }
        }

        private int _variableIndex = 1;

        private IEnumerable<Tuple<SetVarExpression[], FormulaBind.Bind[]>> ProduceVarSetHelper(Quorum[] constantQuorums,
            Quorum[] quorums, int level)
        {
            int myLevel = level;
            if (myLevel == 0 || constantQuorums.Length + quorums.Length == 0)
            {
                yield return new Tuple<SetVarExpression[], FormulaBind.Bind[]>(new SetVarExpression[] { },
                    new FormulaBind.Bind[] { });
                yield break;
            }

            for (var i = 0; i < constantQuorums.Length; ++i)
            {
                var newConstants = constantQuorums.ToList();
                newConstants.RemoveAt(i);
                foreach (var tuple in ProduceVarSetHelper(newConstants.ToArray(), quorums, myLevel - 1))
                {
                    yield return new Tuple<SetVarExpression[], FormulaBind.Bind[]>(
                        tuple.Item1.Add(new SetVarExpression(constantQuorums[i].Name)).ToArray(), tuple.Item2);
                }
            }

            for (var i = 0; i < quorums.Length; ++i)
            {
                foreach (var tuple in ProduceVarSetHelper(constantQuorums, quorums, level - 1))
                {
                    string varName = $"{quorums[i].Name}_{StringUtils.IntToUniqueString(_variableIndex++)}";
                    yield return new Tuple<SetVarExpression[], FormulaBind.Bind[]>(
                        tuple.Item1.Add(new SetVarExpression(varName)).ToArray(),
                        tuple.Item2.Add(new FormulaBind.Bind(FormulaBind.BindType.ForallSet, quorums[i].Name, varName))
                            .ToArray());
                }
            }
        }
    }
}
