using System;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser
{
    public class Program
    {
        private static readonly Dictionary<string, Identifier> Identifiers = new Dictionary<string, Identifier>();
        private static readonly List<Formula> Formulas = new List<Formula>();

        private static Identifier ParseIdentifier(ArrayView<Token> tokens)
        {
            var constant = false;
            var tokenIndex = 0;            
            if(tokens[tokenIndex].Type == SyntaxKind.ConstantKeyword)
            {
                constant = true;
                ++tokenIndex;
            }
            switch (tokens[tokenIndex].Type)
            {
                case SyntaxKind.NaturalKeyword:
                    return ParseNaturalDefinition(constant, tokens.Skip(tokenIndex + 1));
                case SyntaxKind.QuorumKeyword:
                    return ParseQuorumDefinition(constant, tokens.Skip(tokenIndex + 1).ToArray());
                default:
                    return null;
            }
        }

        private static Identifier ParseQuorumDefinition(bool constant, ArrayView<Token> tokens)
        {
            if (tokens[0].GeneralType != SyntaxGeneralType.VariableName) throw new IllegalNaturalName(tokens[0]);
            if (tokens[1].GeneralType != SyntaxGeneralType.ComparisonOperators) throw new IllegalNaturalName(tokens[1]);
            return new Quorum(constant, tokens[0].Value, tokens[1].Type, NaturalExpression.Parse(tokens.Skip(2).ToArray()));
        }

        private static Identifier ParseNaturalDefinition(bool constant, ArrayView<Token> tokens)
        {
            var token = tokens.Single();
            if (token.Type != SyntaxKind.VariableNameToken) throw new IllegalNaturalName(token);
            return new Natural(constant, token.Value);
        }

        public static void ParseCode(Token[] tokens)
        {
            var identifier = ParseIdentifier(tokens);
            if(identifier != null)
            {
                if (Identifiers.ContainsKey(identifier.Name))
                {
                    throw new MultipleDefinitionsOfIdentifier(tokens[0]);
                }
                Identifiers[identifier.Name] = identifier;
                return;
            }
        }

        public static void Main(string[] args)
        {
            /**foreach(var t in Tokenizer.Tokenize("..\\..\\..\\..\\..\\bosco2.folthreshold").SelectMany(tokens => tokens))
            {
                
            }*/
            ParseCode(new Tokenizer("quorum A >= 2n - 2t", 0).Tokenize().ToArray());
            Console.Read();
        }
    }
}
