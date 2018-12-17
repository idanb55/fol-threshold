using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.Parser;

namespace FolThresholdParser
{
    public class Program
    {
        private static readonly Dictionary<string, Identifier> Identifiers = new Dictionary<string, Identifier>();
        private static readonly List<Formula> Formulas = new List<Formula>();

        public static void ParseCode(Token[] tokens)
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

                var formula = Formula.Parse(tokens);
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

        public static void Main(string[] args)
        {
            try
            {
                foreach (var t in Tokenizer.Tokenize("..\\..\\..\\..\\..\\bosco2.folthreshold"))
                {
                    ParseCode(t.ToArray());
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.Message);
            }

            Console.Read();
        }
    }
}
