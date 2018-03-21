

fs = require ("fs")
cp = require ("child_process")


passed = 0;
failed = 0;
fnames = [];

files = fs.readdirSync("./test")
files.forEach(function (each) {
    res = cp.spawnSync ("agda" , [ "test/" + each + "/" + each + ".agda" ])
    out = res.output.toString("utf8").split("\n").filter(function (line) {return (line.indexOf("Checking") + line.indexOf(each + "/" + each + ".agda") == -2)})
    out.splice(-3 , 3)
    out = out.join("\n")
    cout = fs.readFileSync("test/" + each + "/" + each + ".err").toString("utf8").split("\n")
    cout = cout.join("\n")
    if (cout == out) {
      passed = passed + 1
      console.log(each + "\x1b[32m" + " passed" + "\x1b[0m")
    } else {
      failed = failed + 1
      fnames.push(each)
      console.log(each + "\x1b[31m" + " failed" + "\x1b[0m")
    }
})


console.log("Passed Tests : " + passed);
console.log("Failed Tests : " + failed);
console.log("Failed Test Names : \n  " + fnames.join("\n  "))
