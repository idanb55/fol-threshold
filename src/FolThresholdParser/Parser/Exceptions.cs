using System;

namespace FolThresholdParser.Parser
{
    public class ParserTokenException : Exception
    {
        private static string GetMessage(string message, Token token)
        {
            return $"  {token.Code}\n  {new string(' ', token.Start)}^\n{message}";
        }

        public ParserTokenException(string message, Token token) : base(GetMessage(message, token))
        {
        }

        public ParserTokenException(string message, Token token, Exception inner) : base(GetMessage(message, token), inner)
        {
        }
    }
}
