using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;

namespace FolThresholdParser.FolThresholdSystem
{
    public class FolThresholdSystem
    {
        public const string UniversalSetIdentifier = "U";

        private readonly Dictionary<string, Identifier> _identifiers = new Dictionary<string, Identifier>();
        private readonly List<Specification> _formulas = new List<Specification>();

        public FolThresholdSystem()
        {
            //_identifiers[EmptysetIdentifier] = new Quorum(true, EmptysetIdentifier, SyntaxKind.EqualToken,new NatConstExpression(0));

            _identifiers[UniversalSetIdentifier] = new Quorum(true, UniversalSetIdentifier, SyntaxKind.EqualToken,
                new NatVarExpression("n"));

            _formulas.Add(new Specification
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
                    if (_identifiers.ContainsKey(identifier.Name))
                    {
                        throw new ParserTokenException("Multiple definitions of the same identifier", tokens[0]);
                    }

                    _identifiers[identifier.Name] = identifier;
                    return;
                }

                var formula = Specification.Parse(tokens);
                if (formula != null)
                {
                    _formulas.Add(formula);
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
            foreach (var quorum in _identifiers.Values.OfType<Quorum>().Where(quo => !quo.Constant))
            {
                yield return $"type quorum_{quorum.Name.ToLower()} # {Tokenizer.Keywords[quorum.Operation]} {quorum.Expression}";
            }

            foreach (var quorum in _identifiers.Values.OfType<Quorum>())
            {
                if (quorum.Constant) yield return $"relation member_{quorum.Name.ToLower()}(N:node)";
                else yield return $"relation member_{quorum.Name.ToLower()}(N:node, Q:quorum_{quorum.Name.ToLower()})";
            }

            yield return $"relation member_emptyset(N:node)";
            yield return "axiom forall N:node. ~member_emptyset(N)";

            foreach (var formula in _formulas.Where(spec => spec.Conjecture))
            {
                yield return "axiom " + formula.ToBoundIvyAxiom(_identifiers);
            }
        }

        public IEnumerable<string> AssertThresholdSmt2()
        {
            yield return "(set-logic ALL_SUPPORTED)";
            yield return "(set-info :status unsat)";

            yield return string.Empty;

            foreach (var quorum in _identifiers.Values.OfType<Natural>())
            {
                yield return $"(declare-fun {quorum.Name} () Int)";
            }

            yield return string.Empty;

            foreach (var quorum in _identifiers.Values.OfType<Quorum>())
            {
                yield return $"(declare-fun {quorum.Name} () (Set Int))";
            }

            yield return string.Empty;

            foreach (var spec in _formulas.Where(spec => !spec.Conjecture))
            {
                yield return $"(assert ({spec.Formula.GetSmtAssert(_identifiers)}))";
            }

            yield return string.Empty;

            foreach (var quorum in _identifiers.Values.OfType<Quorum>().Where(quorum => !quorum.Constant))
            {
                yield return $"(assert (subset {quorum.Name} {UniversalSetIdentifier}))";
            }

            yield return string.Empty;

            foreach (var quorum in _identifiers.Values.OfType<Quorum>())
            {
                var axiom = new NaturalFormula(new NatCardExpression(new SetVarExpression(quorum.Name)), quorum.Operation, quorum.Expression);
                yield return $"(assert ({axiom.GetSmtAssert(_identifiers)}))";
            }

            yield return string.Empty;

            foreach (var spec in _formulas.Where(spec => spec.Conjecture))
            {
                yield return $"; {spec}";
                yield return $"(assert ({spec.Formula.Negate().Release(FormulaBind.BindType.ExistsSet).GetSmtAssertActual(_identifiers)}))";
            }
        }
    }
}
