using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;

namespace FolThresholdParser.FolThresholdSystem
{
    public class FolThresholdSystem
    {
        private readonly Dictionary<string, Identifier> _identifiers = new Dictionary<string, Identifier>();
        private readonly List<Specification> _formulas = new List<Specification>();

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
                yield return $"type quorum_{quorum.Name} # {Tokenizer.Keywords[quorum.Operation]} {quorum.Expression}";
            }

            foreach (var quorum in _identifiers.Values.OfType<Quorum>())
            {
                if (quorum.Constant) yield return $"relation {quorum.Name}(N:node)";
                else yield return $"relation member_{quorum.Name}(N:node, Q:quorum_{quorum.Name})";
            }

            foreach (var formula in _formulas) // where conjecture
            {
                yield return formula.ToString(); //.ToBoundIvyAxiom(_identifiers);
            }
        }
    }
}
