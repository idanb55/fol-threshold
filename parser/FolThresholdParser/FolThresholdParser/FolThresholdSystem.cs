using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.BapaFormula;
using FolThresholdParser.FolThresholdEntities;
using FolThresholdParser.Parser;

namespace FolThresholdParser
{
    public class FolThresholdSystem
    {
        private readonly Dictionary<string, Identifier> _identifiers = new Dictionary<string, Identifier>();
        private readonly List<Formula> _formulas = new List<Formula>();

        public void ParseCode(Token[] tokens)
        {
            try
            {
                if (tokens.Length == 0) return;

                var identifier = Identifier.Parse(tokens);
                if (identifier != null)
                {
                    if (_identifiers.ContainsKey(identifier.Name.ToLower()))
                    {
                        throw new ParserTokenException("Multiple definitions of the same identifier", tokens[0]);
                    }

                    _identifiers[identifier.Name.ToLower()] = identifier;
                    return;
                }

                var formula = Formula.Parse(tokens);
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

        public BapaFormula.BapaFormula ToBapaFormula()
        {
            var constants = _identifiers.Values.Where(identifier => identifier.Constant);
            var assumptions = _formulas.Where(formula => !formula.Conjecture);
            var conjectures = _formulas.Where(formula => formula.Conjecture);

            var quorumAssumption = _identifiers.Values.OfType<Quorum>().Select(quorum => quorum.GetQuorumAssumption());
            BapaFormula.BapaFormula freeFormula = new BapaImpl(
                new BapaFormulaOperation(BapaFormulaOperation.NatRelation.And,
                    assumptions.Select(assumption => assumption.ToBoundBapaFormula(_identifiers)).Concat(quorumAssumption).ToArray()),
                new BapaFormulaOperation(BapaFormulaOperation.NatRelation.And,
                    conjectures.Select(assumption => assumption.ToBoundBapaFormula(_identifiers)).ToArray()));

            return constants.Aggregate(freeFormula,
                (current, identifier) =>
                    new BapaBind(
                        identifier is Natural ? BapaBind.BapaBindType.Forallnat : BapaBind.BapaBindType.Forallset,
                        identifier.Name, current));
        }
    }
}
