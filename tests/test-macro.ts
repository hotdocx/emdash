function $hello() {
    return "Hello from macro!";
}

let myvar = $hello!();

console.log($hello!());