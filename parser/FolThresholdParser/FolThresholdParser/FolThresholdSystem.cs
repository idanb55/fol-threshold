using System;
using System.Collections.Generic;
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
                    if (_identifiers.ContainsKey(identifier.Name))
                    {
                        throw new ParserTokenException("Multiple definitions of the same identifier", tokens[0]);
                    }

                    _identifiers[identifier.Name] = identifier;
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
    }
}
