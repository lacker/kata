// Whether the sequence from s[i] to s[j] inclusive is a palindrome
fn is_palindrome(s: &[char]) -> bool {
    if s.len() < 2 {
        return true;
    }
    let last = s.len() - 1;
    if s[0] != s[last] {
        return false;
    }
    is_palindrome(&s[1..last])
}

fn is_almost_palindrome(s: &[char]) -> bool {
    if s.len() < 3 {
        return true;
    }
    let last = s.len() - 1;
    if s[0] == s[last] {
        return is_almost_palindrome(&s[1..last]);
    }
    is_palindrome(&s[1..]) || is_palindrome(&s[..last])
}

fn test_almost_palindrome(s: &str) {
    let chars: Vec<char> = s.chars().collect();
    println!("is_almost_palindrome(\"{}\") = {}", s, is_almost_palindrome(&chars));
}

fn main() {
    test_almost_palindrome("");
    test_almost_palindrome("x");
    test_almost_palindrome("oo");
    test_almost_palindrome("boof");
    test_almost_palindrome("boofb");
    test_almost_palindrome("bbboofbbb");
    test_almost_palindrome("fboofb");
    test_almost_palindrome("pogop");
    test_almost_palindrome("pogrop");
    test_almost_palindrome("pogrop");
    test_almost_palindrome("pogroop");
    test_almost_palindrome("pogrrop");
}
